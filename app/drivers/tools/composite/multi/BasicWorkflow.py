import os
import time
from multiprocessing import Lock
from multiprocessing.pool import ThreadPool
from os.path import join
from queue import Queue
from typing import Any
from typing import cast
from typing import Dict
from typing import List
from typing import Set
from typing import Union

from watchdog.events import DirCreatedEvent
from watchdog.events import FileCreatedEvent
from watchdog.events import FileSystemEvent
from watchdog.events import FileSystemEventHandler
from watchdog.observers import Observer

from app.core import configuration
from app.core import definitions
from app.core import values
from app.core.main import create_task_identifier
from app.core.main import create_task_image_identifier
from app.core.task import analyze
from app.core.task import fuzz
from app.core.task import repair
from app.core.task import select
from app.core.task import task
from app.core.task.typing.CompositeSequence import CompositeSequence
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.task.typing.TaskType import TaskType
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.drivers.tools.composite.AbstractCompositeTool import AbstractCompositeTool
from app.drivers.tools.MockTool import MockTool


class BasicWorkflow(AbstractCompositeTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        # preferably change to a container with the dependencies ready to reduce setup time
        self.image_name = "ubuntu:20.04"
        self.process_count = 12
        self.event_processor_count = 4
        self.exit_message = "quit"

    def run_composite(
        self,
        dir_info: DirectoryInfo,
        benchmark: AbstractBenchmark,
        bug_info,  # Entry from  meta-data.json
        composite_config_info,  # Task Profile
        container_config_info,  # Container Profile
        run_index: str,  # Specific iteration of the workflow run
        hash: Any,  # Hash, to be used for unique locations
    ):
        super(BasicWorkflow, self).run_composite(
            dir_info,
            benchmark,
            bug_info,
            composite_config_info,
            container_config_info,
            run_index,
            hash.hexdigest()[:8],
        )
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """
        self.pool = ThreadPool(processes=self.process_count)
        self.message_queue: Queue[Union[str, FileSystemEvent]] = Queue()
        self.observer = Observer()
        self.mutex = Lock()
        self.observed: Set[Any] = set()

        self.emit_debug(composite_config_info)
        composite_sequence = composite_config_info[self.key_composite_sequence]
        tool_tag = composite_config_info.get(definitions.KEY_TOOL_TAG, "")

        self.emit_normal("setting up workflow")
        self.emit_debug(composite_sequence)

        root_dir = join(
            values.dir_main,
            "composite_workspace",
            "run-{}".format(hash.hexdigest()[:8]),
        )
        os.makedirs(root_dir, exist_ok=True)
        self.root_dir = root_dir

        self.task_mappings = self.make_task_mappings(root_dir)
        self.bug_info = bug_info

        tool_map: Dict[TaskType, List[AbstractTool]] = {}

        for task_type, tools in composite_sequence.items():
            tool_map[task_type] = []
            for tool_name in tools:
                if tool_name == "mock":
                    tool = cast(AbstractTool, MockTool())
                else:
                    tool = configuration.load_tool(tool_name, task_type)

                self.emit_debug(tool.bindings)
                tool.bindings = tool.bindings or {}
                tool.bindings.update(self.task_mappings[task_type])
                self.emit_debug(tool.bindings)

                tool.check_tool_exists()
                image_name = create_task_image_identifier(
                    benchmark,
                    tool,
                    bug_info,
                    tool_tag,
                )
                experiment_image_id = task.prepare_experiment(
                    benchmark,
                    bug_info,
                    composite_config_info[self.key_cpus],
                    [],
                    tool_tag,
                )
                task.prepare_experiment_tool(
                    experiment_image_id,
                    tool,
                    composite_config_info,
                    dir_info,
                    image_name,
                    tool_tag,
                )
                tool_map[task_type].append(tool)
                # key = create_task_identifier(
                #    benchmark,
                #    composite_config_info,
                #    container_config_info,
                #    bug_info,
                #    tool,
                #    str(run_index),
                #    tool_tag,
                # )

                # task.run(
                #    benchmark,
                #    tool,
                #    bug_info,
                #    composite_config_info,
                #    container_config_info,
                #    key,
                #    composite_config_info[self.key_cpus],
                #    composite_config_info[self.key_gpus],
                #    run_index,
                #    image_name,
                # )
        self.emit_highlight("Done with setup!")

        self.emit_highlight("Preparing watcher")
        watcher_handle = self.pool.apply_async(self.watcher)

        self.emit_highlight("Preparing workers")
        for _ in range(self.event_processor_count):
            self.pool.apply_async(self.event_worker)

        if "analyze" in tool_map:
            for tool in tool_map["analyze"]:
                self.pool.apply_async(
                    self.run_analysis,
                    [
                        dir_info,
                        benchmark,
                        bug_info,
                        composite_config_info,
                        container_config_info,
                        run_index,
                        hash,
                        tool,
                    ],
                )
        elif "fuzz" in tool_map:
            for tool in tool_map["fuzz"]:
                if tool == "aflplusplus":
                    os.makedirs(join(self.root_dir, "default"))
                    os.makedirs(join(self.root_dir, "default", "crashes"))
                    os.makedirs(join(self.root_dir, "default", "queue"))
                self.pool.apply_async(
                    self.run_fuzz,
                    [
                        dir_info,
                        benchmark,
                        bug_info,
                        composite_config_info,
                        container_config_info,
                        run_index,
                        hash,
                        tool,
                    ],
                )
        else:
            self.observer.stop()
            for _ in range(self.event_processor_count):
                self.message_queue.put("exit")
            self.emit_error("No supported starter for the process")

        watcher_handle.wait()
        self.pool.terminate()
        self.emit_highlight("Terminated")
        # pass

        timeout_h = str(composite_config_info[self.key_timeout])
        # start running
        self.timestamp_log_start()

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def run_analysis(
        self,
        dir_info: DirectoryInfo,
        benchmark: AbstractBenchmark,
        bug_info,  # Entry from  meta-data.json
        composite_config_info,  # Task Profile
        container_config_info,  # Container Profile
        run_index,  # Specific iteration of the workflow run
        hash: Any,  # Hash, to be used for unique locations
        tool: AbstractTool,
    ):
        values.task_type.set("analyze")
        tool_tag = composite_config_info.get(definitions.KEY_TOOL_TAG, "")
        image_name = create_task_image_identifier(
            benchmark,
            tool,
            bug_info,
            tool_tag,
        )

        key = create_task_identifier(
            benchmark,
            composite_config_info,
            container_config_info,
            bug_info,
            tool,
            str(run_index),
            tool_tag,
        )

        task.run(
            benchmark,
            tool,
            bug_info,
            composite_config_info,
            container_config_info,
            key,
            composite_config_info[self.key_cpus],
            composite_config_info[self.key_gpus],
            run_index,
            image_name,
            hash,
        )

    def run_fuzz(
        self,
        dir_info: DirectoryInfo,
        benchmark: AbstractBenchmark,
        bug_info,  # Entry from  meta-data.json
        composite_config_info,  # Task Profile
        container_config_info,  # Container Profile
        run_index,  # Specific iteration of the workflow run
        hash: Any,  # Hash, to be used for unique locations
        tool: AbstractTool,
    ):
        values.task_type.set("fuzz")
        tool_tag = composite_config_info.get(definitions.KEY_TOOL_TAG, "")
        image_name = create_task_image_identifier(
            benchmark,
            tool,
            bug_info,
            tool_tag,
        )

        key = create_task_identifier(
            benchmark,
            composite_config_info,
            container_config_info,
            bug_info,
            tool,
            str(run_index),
            tool_tag,
        )

        task.run(
            benchmark,
            tool,
            bug_info,
            composite_config_info,
            container_config_info,
            key,
            composite_config_info[self.key_cpus],
            composite_config_info[self.key_gpus],
            run_index,
            image_name,
            hash,
        )

    class FileCreationHandler(FileSystemEventHandler):
        def __init__(self, q: Queue):
            # print("Initializing")
            self.q = q

        def on_created(self, event: FileSystemEvent):
            # print("Created!")
            self.q.put(event)

    def watcher(self):
        event_handler = BasicWorkflow.FileCreationHandler(self.message_queue)
        self.emit_highlight("Observing {}".format(self.root_dir))
        self.observer.schedule(event_handler, self.root_dir, recursive=True)
        self.observer.start()

        try:
            while self.observer.is_alive():
                self.observer.join(1)
        finally:
            self.observer.stop()
            self.observer.join()

    def pre_process_event(self, event: FileSystemEvent):
        if self.filter_event(event):
            self.emit_debug("Did not filter {}".format(event))
            with self.mutex:
                if event.src_path not in self.observed:
                    self.observed.add(event.src_path)
                    new_file = True
                else:
                    new_file = False

            self.emit_debug("Is new file? {}".format(new_file))
            if new_file:
                time.sleep(1)  # HACK: make sure file is written to
                return True
        self.emit_debug("Filtered {}".format(event))
        return False

    def filter_event(self, event: FileSystemEvent):
        self.emit_debug("Filtering - not really")
        return True

    def process_event(self, event: FileSystemEvent):
        self.emit_debug("Processing!")
        self.emit_debug(event)
        if os.path.basename(event.src_path) == "quit":
            for _ in range(self.process_count):
                self.emit_debug("Time to die")
                self.message_queue.put(self.exit_message)

        if (
            os.path.commonprefix(
                [event.src_path, list(self.task_mappings["repair"].keys())[0]]
            )
            == list(self.task_mappings["repair"].keys())[0]
        ):
            self.emit_highlight("Repair update")
            pass
        elif (
            os.path.commonprefix(
                [event.src_path, list(self.task_mappings["analyze"].keys())[0]]
            )
            == list(self.task_mappings["analyze"].keys())[0]
        ):
            self.emit_highlight("Analyze Update")
            pass
        elif (
            os.path.commonprefix(
                [event.src_path, list(self.task_mappings["fuzz"].keys())[0]]
            )
            == list(self.task_mappings["fuzz"].keys())[0]
        ):
            self.emit_highlight("Fuzz Update")
            pass
        elif (
            os.path.commonprefix(
                [event.src_path, list(self.task_mappings["validate"].keys())[0]]
            )
            == list(self.task_mappings["validate"].keys())[0]
        ):
            self.emit_highlight("Validate Update")
            pass
        elif (
            os.path.commonprefix(
                [event.src_path, list(self.task_mappings["select"].keys())[0]]
            )
            == list(self.task_mappings["select"].keys())[0]
        ):
            self.emit_highlight("Select Update")
            pass
        elif (
            os.path.commonprefix(
                [event.src_path, list(self.task_mappings["localize"].keys())[0]]
            )
            == list(self.task_mappings["localize"].keys())[0]
        ):
            self.emit_highlight("Select Update")
            pass
        # meta_data_fpath = event.src_path
        # crash_folder = os.path.dirname(event.src_path)
        # hash = os.path.basename(crash_folder)
        # meta_data_fpath = os.path.abspath(meta_data_fpath)

        # with open(meta_data_fpath) as f:
        #     c = f.read()

        # md = json.loads(c)[0]

        # subject = md["subject"]
        # bug_id = md["bug_id"]

        # tool = os.getenv("TOOL")

        # cerberus_input_dir = f"cerberus/benchmark/vulnloc/{subject}/{bug_id}-{hash}"
        # cerberus_outpt_dir = f"cerberus-vulnloc-out/{subject}-{bug_id}"

        # shutil.copytree(f"vulnloc-benchmark/{subject}/{bug_id}", cerberus_input_dir)

        # tests_dir = f"{cerberus_input_dir}/tests"
        # os.makedirs(tests_dir, exist_ok=True)

        # shutil.copytree(f"{crash_folder}/crashes", tests_dir, dirs_exist_ok=True)
        # shutil.copytree(f"{crash_folder}/non-crashes", tests_dir, dirs_exist_ok=True)

        # os.makedirs(cerberus_outpt_dir, exist_ok=True)
        # os.makedirs("cerberus/e2e_logs", exist_ok=True)
        # print(f"~~~~~ Starting CERBERUS ({tool}) on {hash} ~~~~~")

        # cerb_str_cmd = f"./bin/cerberus --task-type repair --benchmark vulnloc --tool {tool} --special-meta {meta_data_fpath} --bug-index=1 --tool-tag {hash} --debug &> e2e_logs/cerberus_{hash}.log"

    def event_worker(self):
        while True:
            event = self.message_queue.get()
            self.emit_debug("Got message {}".format(event))
            if isinstance(event, str) and event == self.exit_message:
                if self.observer.is_alive():
                    self.observer.stop()
                break
            if self.pre_process_event(event):
                try:
                    self.process_event(event)
                except Exception as e:
                    print(f"Exception when processing {event}:\n {e}")

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        super().save_artifacts(dir_info)

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")

        return self.stats

    def make_task_mappings(self, root_dir):
        task_mappings = {
            "fuzz": {join(root_dir, "fuzzing"): {"bind": "/output", "mode": "rw"}},
            "repair": {join(root_dir, "repair"): {"bind": "/output", "mode": "rw"}},
            "analyze": {join(root_dir, "analyze"): {"bind": "/output", "mode": "rw"}},
            "select": {join(root_dir, "select"): {"bind": "/output", "mode": "rw"}},
            "validate": {join(root_dir, "validate"): {"bind": "/output", "mode": "rw"}},
            "localize": {join(root_dir, "localize"): {"bind": "/output", "mode": "rw"}},
        }
        self.emit_debug(task_mappings)
        for task in task_mappings.values():
            for key in task.keys():
                os.makedirs(key, exist_ok=True)

        return task_mappings
