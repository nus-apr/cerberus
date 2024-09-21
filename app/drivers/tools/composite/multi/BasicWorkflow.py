import copy
import hashlib
import json
import os
import shutil
import httpx
import sys
import time
import traceback
from copy import deepcopy
from multiprocessing import Lock
from multiprocessing.pool import ThreadPool
from multiprocessing.synchronize import Lock as LockType
from os.path import basename
from os.path import dirname
from os.path import join
from queue import Queue
from queue import PriorityQueue
from typing import Any
from typing import Callable
from typing import cast
from typing import Dict
from typing import List
from typing import Optional
from typing import Set
from typing import Tuple
from typing import Union
import base64

from jsonschema import Draft7Validator
from watchdog.events import FileSystemEvent
from watchdog.observers.polling import PollingObserver as Observer

from app.core import configuration
from app.core import definitions
from app.core import reader
from app.core import values
from app.core import writer
from app.core.identifiers import create_task_identifier
from app.core.identifiers import create_task_image_identifier
from app.core.metadata.MetadataValidationSchemas import general_section_schema
from app.core.task import task
from app.core.task.dir_info import generate_tool_dir_info
from app.core.task.image import prepare_experiment_image
from app.core.task.image import prepare_experiment_tool
from app.core.task.stats.CompositeToolStats import CompositeToolStats
from app.core.task.TaskStatus import TaskStatus
from app.core.task.typing.CompositeSequence import CompositeSequence
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.task.typing.TaskType import CompositeTaskType
from app.core.task.typing.TaskType import TaskType
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.drivers.tools.composite.AbstractCompositeTool import AbstractCompositeTool
from app.drivers.tools.composite.multi.basic.FileCreationHandler import (
    FileCreationHandler,
)
from app.drivers.tools.MockTool import MockTool

active_jobs_lock: LockType


# Due to the way python multiprocess works,
# we cannot pass a lock to the pool initializer by just seeting a
# field on the object, similarly to how it is done in the UI module
# (the UI module is using in process threads and the lock is not shared across process, has to be reworked).
# Instead, we need to use a global variable which is per process.
# This is not ideal, but it is the correct way to make it work.
def init_pool_processes(active_jobs_lock_x: LockType) -> None:
    global active_jobs_lock
    active_jobs_lock = active_jobs_lock_x


class BasicWorkflow(AbstractCompositeTool):
    key_task_tag: str = "task_tag"
    key_image_tag: str = "image_tag"
    key_real_type = "real_type"

    def __init__(self) -> None:
        self.name = basename(__file__)[:-3].lower()
        super().__init__(self.name)
        # preferably change to a container with the dependencies ready to reduce setup time
        self.image_name = "ubuntu:22.04"
        self.exit_message = "quit"  # Message for terminating the flow
        self.exit_message_delayed = (
            "quit_delayed"  # Message for a termination that will happen after a delay
        )
        self.patch_validation_map = {}
        self.repair_retry_map = {}
        self.vulnerability_validation_map = {}
        self.execution_counters: Dict[CompositeTaskType, int] = {}
        self.crash_signature_set = set()
        self.last_crash = 0
        self.active_jobs = 0
        self.max_retry_count = 1

    def invoke_advanced(
        self,
        dir_info: DirectoryInfo,
        benchmark: AbstractBenchmark,
        bug_info: Dict[str, Any],  # Entry from  meta-data.json
        task_config_info: Dict[str, Any],  # Task Profile
        container_config_info: Dict[str, Any],  # Container Profile
        run_index: str,  # Specific iteration of the workflow run
        hash: Any,  # Hash, to be used for unique locations
    ) -> None:
        """
        Entry point for the workflow.
        The function parses the composite sequence proivded in the task_config_info
        and then starts an "initial tool" - fuzzer, localizer, repair tool, in that order of preference.
        """
        super(BasicWorkflow, self).invoke_advanced(
            dir_info,
            benchmark,
            bug_info,
            task_config_info,
            container_config_info,
            run_index,
            hash,
        )
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        cpu_count = len(task_config_info[self.key_cpus])
        self.cpu_count = cpu_count

        self.task_config_info = task_config_info

        self.file_watch_pool_count = min(15, max(8, cpu_count // 8))
        self.file_processor_count = min(20, max(8, cpu_count // 8))

        global_job_lock = Lock()
        self.file_pool = ThreadPool(
            processes=self.file_watch_pool_count,
        )

        self.processed_file_pool = ThreadPool(
            processes=self.file_processor_count,
            initializer=init_pool_processes,
            initargs=(global_job_lock,),
        )

        composite_sequence: CompositeSequence = cast(
            CompositeSequence, task_config_info[self.key_composite_sequence]
        )

        active_fuzzers = len(
            list(
                filter(
                    lambda x: not x.get("ignore", False),
                    composite_sequence.get("fuzz", []),
                )
            )
        )

        self.task_pool: ThreadPool = ThreadPool(
            cpu_count,
            initializer=init_pool_processes,
            initargs=(global_job_lock,),
        )

        self.patch_validation_map_lock = Lock()
        self.repair_retry_map_lock = Lock()
        self.vulnerability_validation_map_lock = Lock()
        self.message_queue: Queue[Union[str, FileSystemEvent]] = Queue()
        self.observer = Observer()
        self.cpu_queue: Queue[str] = Queue()
        self.cpu_request_queue: PriorityQueue[(int, str)] = PriorityQueue()
        self.tool_priority: Dict[CompositeTaskType, int] = {
            "validate": 1,
            "bisect": 2,
            "repair": 3,
            "iterative-repair": 4,
            "localize": 5,
            "analyze": 6,
            "fuzz": 7,
            "crash-analyze": 8,
        }
        # TODO implement gpu queue

        if "fuzz" in composite_sequence:
            available_cpus = len(task_config_info[self.key_cpus])
            import math

            task_count = max(active_fuzzers + 5, int(math.ceil(0.5 * available_cpus)))
            for i in task_config_info[self.key_cpus][:task_count]:
                self.cpu_queue.put(str(i))
                self.emit_normal(f"allocating cpu {i}")
            task_config_info["fuzzer_cpu"] = int(math.floor(0.7 * available_cpus))
        else:
            for i in task_config_info[self.key_cpus]:
                self.cpu_queue.put(str(i))
                self.emit_normal(f"allocating cpu {i}")

        self.mutex = Lock()
        self.observed: Set[Any] = set()
        self.request_queue_lock = Lock()

        self.emit_debug(task_config_info)
        root_tool_tag = task_config_info.get(definitions.KEY_TOOL_TAG, "")

        self.emit_normal("setting up workflow")
        # self.emit_debug(composite_sequence)

        root_dir = join(
            values.dir_composite_workspace,
            "run-{}".format(hash.hexdigest()[: values.hash_suffix_length]),
        )
        self.root_dir = root_dir
        self.root_artifact_dir = join(root_dir, "artifacts")
        self.root_setups_dir = join(root_dir, "setups")
        self.root_logs_dir = join(root_dir, "logs")

        for x in [
            self.root_dir,
            self.root_artifact_dir,
            self.root_setups_dir,
            self.root_logs_dir,
        ]:
            os.makedirs(x, exist_ok=True)

        self.root_task_mappings = self.make_root_task_mappings(self.root_artifact_dir)
        self.bug_info = bug_info

        self.tool_map: Dict[
            CompositeTaskType, List[Tuple[Callable[[], AbstractTool], str, str, str]]
        ] = {}

        self.session_key = values.session_identifier.get("NAN")

        for task_type, tools in composite_sequence.items():
            self.tool_map[task_type] = []
            for tool_info in tools:
                tag_fragments: List[str] = []
                if root_tool_tag:
                    tag_fragments.append(root_tool_tag)

                tool_name = tool_info["name"]
                if tool_info.get("ignore", False):
                    # self.emit_debug(f"Skip {tool_name}")
                    continue

                tool_local = bool(tool_info.get("local", False))
                # self.emit_debug(f"Local: {tool_local}")

                tool_params = tool_info.get("params", "")

                extra_tool_tag = tool_info.get("tag", "")
                if extra_tool_tag:
                    tag_fragments.append(extra_tool_tag)

                tool_tag = "-".join(tag_fragments)

                real_type = tool_info.get(
                    "type", task_type
                )  # override the type when in "special" (crash-analyze) types
                if tool_name == "mock":
                    tool_constructor: Callable[[], AbstractTool] = lambda: cast(
                        AbstractTool, MockTool()
                    )
                    tool = tool_constructor()
                else:

                    def make_tool_constructor(
                        tool_name: str, real_type: str, tool_tag: str, tool_local: bool
                    ) -> Callable[[], AbstractTool]:
                        def tool_constructor() -> AbstractTool:
                            t = configuration.load_tool(tool_name, real_type)
                            t.tool_tag = tool_tag
                            t.bindings = t.bindings or {}
                            t.locally_running = tool_local
                            return t

                        return tool_constructor

                    tool_constructor = make_tool_constructor(
                        copy.deepcopy(tool_name),
                        copy.deepcopy(real_type),
                        copy.deepcopy(tool_tag),
                        copy.deepcopy(tool_local),
                    )
                    tool = tool_constructor()
                    tool.tool_tag = tool_tag

                tool.bindings = tool.bindings or {}

                tool.ensure_tool_exists()

                self.tool_map[task_type].append(
                    (tool_constructor, tool_params, tool_tag, real_type)
                )

        # self.emit_highlight("Done with setup!")

        self.emit_highlight("Preparing watcher")
        watcher_handle = self.file_pool.apply_async(
            self.watcher, error_callback=self.error_callback_handler
        )

        self.emit_highlight("Preparing workers")
        for _ in range(self.file_watch_pool_count - 1):
            self.file_pool.apply_async(
                self.event_worker, error_callback=self.error_callback_handler
            )

        self.proto_args = (
            dir_info,
            benchmark,
            bug_info,
            task_config_info,
            container_config_info,
            run_index,
            hash,
        )
        # start running
        self.timestamp_log_start()

        if not self.do_step(
            bug_info,
            None,
            None,
            [
                "analyze",
                "fuzz",
                "crash-analyze",
                "bisect",
                "localize",
                "slice",
                "repair",
                "validate",
                "select",
                "iterative-repair",
            ],
            [],
        ):
            self.observer.stop()  # type:ignore
            for _ in range(self.file_processor_count):
                self.message_queue.put("exit")
            # self.emit_error("No supported starter for the process")

        watcher_handle.wait()
        self.file_pool.terminate()
        self.processed_file_pool.terminate()
        self.task_pool.terminate()
        self.emit_highlight("Terminated")
        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def get_cpu(self, task_type, task_name):
        task_priority = self.tool_priority[task_type]
        with self.request_queue_lock:
            self.cpu_request_queue.put((task_priority, task_name))
        self.emit_normal(
            f"task {task_name} is requesting cpu with priority {task_priority}"
        )

        top_task_name = self.cpu_request_queue.queue[0][1]
        while top_task_name != task_name:
            time.sleep(1)
            top_task_name = self.cpu_request_queue.queue[0][1]

        avail_cpu = self.cpu_queue.get()
        self.emit_normal(f"task {task_name} acquired cpu with priority {task_priority}")
        self.cpu_request_queue.queue.remove((task_priority, task_name))
        return avail_cpu

    def release_cpu(self, cpu_id, task_name):
        self.emit_normal(f"task {task_name} releases cpu")
        self.cpu_queue.put(cpu_id)
        return

    def run_subtask(
        self,
        task_type: TaskType,
        dir_info: DirectoryInfo,
        benchmark: AbstractBenchmark,
        bug_info: Dict[str, Any],  # Entry from  meta-data.json
        task_config_info: Dict[str, Any],  # Task Profile
        container_config_info: Dict[str, Any],  # Container Profile
        run_index: str,  # Specific iteration of the workflow run
        hash: Any,  # Hash, to be used for unique locations
        tool: AbstractTool,
        path: List[
            str
        ],  # List of previously executed tools that were used to reach this point
    ) -> str:
        """
        Common entry point for a subtask, we take the original task tag to not create new images.
        This flow assumes that the run_composite function has prepared all the tags beforehand in order to quickly start new jobs.
        """

        self.emit_highlight(
            f"[STEP] executing tool {tool.name} with tag {tool.tool_tag or ' '} for type {task_type} with crash commit {bug_info.get('commit', 'none')}"
        )
        self.execution_counters[task_type] = (
            self.execution_counters.get(task_type, 0) + 1
        )
        self.emit_highlight(
            f"[COUNT] {task_type} has { self.execution_counters.get(task_type,0) } executions until now"
        )

        # self.emit_debug(f"Bindings are {tool.bindings}")
        tool.bindings = tool.bindings or {}
        new_mappings = self.make_task_mappings(
            tool.name,
            hash.hexdigest()[: values.hash_suffix_length],
            self.root_task_mappings,
            tool.tool_tag,
        )[task_config_info.get(self.key_real_type, task_type)]
        # self.emit_debug(f"New mappings are {new_mappings}")
        for host_dir, _ in new_mappings.items():
            os.makedirs(host_dir, exist_ok=True, mode=0o777)
        tool.bindings.update(new_mappings)
        # self.emit_debug(f"bindings are {tool.bindings}")

        global active_jobs_lock
        with active_jobs_lock:
            self.active_jobs += 1
            # self.emit_debug(f"Active jobs: {self.active_jobs}")

        cpu = None
        key = None
        try:
            values.task_type.set(task_type)
            values.current_task_profile_id.set(task_config_info["id"])
            values.current_container_profile_id.set(task_config_info["id"])
            tool_tag = task_config_info.get(self.key_task_tag, "")
            image_tag = task_config_info.get(self.key_image_tag, "")
            image_name = create_task_image_identifier(
                benchmark, tool, bug_info, image_tag
            )

            # TODO track multiple cpus
            cpu = self.get_cpu(task_type, f"{image_name}-{tool_tag}")

            dir_setup_extended = (
                join(
                    self.root_setups_dir, f"{bug_info[self.key_bug_id]}-{tool_tag}", ""
                )
                if tool_tag
                else None
            )
            dir_logs_extended = join(
                self.root_logs_dir,
                f"{bug_info[self.key_bug_id]}-{tool_tag if tool_tag else tool.name }",
                "",
            )
            key = create_task_identifier(
                benchmark,
                task_config_info,
                container_config_info,
                bug_info,
                tool,
                str(run_index),
                tool_tag,
            )
            values.job_identifier.set(key)
            values.session_identifier.set(self.session_key)

            dir_info = generate_tool_dir_info(
                benchmark.name,
                bug_info[self.key_subject],
                bug_info[self.key_bug_id],
                hash,
                key,
                dir_setup_extended,
                dir_logs_extended,
                list(new_mappings.keys())[0] if tool.locally_running else None,
                tool.locally_running,
            )

            # self.emit_debug(f"Dir info is {dir_info}")
            benchmark.update_dir_info(dir_info, tool.locally_running)

            experiment_image_id = prepare_experiment_image(
                benchmark,
                bug_info,
                task_config_info[self.key_cpus],
                [],
                tool_tag,
                locally_running=tool.locally_running,
            )

            experiment_image_tool_id = prepare_experiment_tool(
                experiment_image_id,
                tool,
                task_config_info,
                dir_info,
                image_name,
                bug_info,
                tool_tag,
            )

            bug_info["image_id"] = experiment_image_tool_id or bug_info["base_image"]

            os.makedirs(dir_logs_extended, exist_ok=True)

            internal_representation_path = join(
                list(new_mappings.keys())[0], definitions.INTERNAL_METADATA_JSON
            )
            with open(internal_representation_path, "w") as f:
                # self.emit_debug(
                #    f"Creating internal representation at {internal_representation_path}"
                # )
                f.write(
                    json.dumps(
                        {
                            "dir_info": dir_info,
                            "task_config_info": task_config_info,
                            "bug_info": bug_info,
                            "path": path + [tool_tag],
                        }
                    )
                )

            self.track_test_count(dir_info, bug_info, key, dir_setup_extended)

            err, _ = task.run(
                benchmark,
                tool,
                bug_info,
                task_config_info,
                container_config_info,
                key,
                [cpu],
                task_config_info[self.key_gpus],
                run_index,
                image_name,
                hash,
                dir_setup_extended,
                dir_logs_extended,
                list(new_mappings.keys())[0] if tool.locally_running else None,
            )
            if err:
                self.stats.error_stats.is_error = True
        except Exception as e:
            tb = traceback.format_exc()
            self.emit_error(e)
            self.emit_error(tb)
            traceback.print_exc(file=sys.stderr)
        finally:
            status = values.experiment_status.get(TaskStatus.NONE)
            if key is not None:
                self.stats.composite_stats.job_statuses[key] = (
                    (
                        1
                        if status == TaskStatus.SUCCESS
                        else (-1 if status == TaskStatus.NONE else -1)
                    ),
                    status,
                )
                self.stats.composite_stats.tool_stats[key] = tool.stats
            self.stats.composite_stats.aggregations[tool.name] = (
                self.stats.composite_stats.aggregations.get(tool.name, [])
                + [tool.stats]
            )

            if cpu is not None:
                self.release_cpu(cpu, f"{image_name}-{tool_tag}")

        with active_jobs_lock:
            self.active_jobs -= 1
            self.emit_debug(f"Active jobs: {self.active_jobs}")
            if self.active_jobs == 0:
                self.message_queue.put(self.exit_message_delayed)
        return list(new_mappings.keys())[0]

    def track_test_count(
        self,
        dir_info: DirectoryInfo,
        bug_info: Dict[str, Any],
        key: str,
        dir_setup: Optional[str],
    ) -> None:
        exploit_input_count = 0
        beningn_input_count = 0
        # if (
        #     self.key_analysis_output not in bug_info
        #     or bug_info[self.key_analysis_output] == []
        # ):
        #     self.emit_warning("No analysis output. I hope you know what you are doing.")

        for analysis_output in bug_info.get(self.key_analysis_output, []):
            if self.key_exploit_inputs in analysis_output:
                for exploit_input_info in analysis_output[self.key_exploit_inputs]:
                    p = join(
                        dir_setup or dir_info["local"]["setup"],
                        str(exploit_input_info["dir"]),
                    )
                    if os.path.exists(p):
                        exploit_input_count += len(os.listdir(p))
                    else:
                        self.emit_warning(
                            f"Path for exploit test list {p} does not exist"
                        )
            if self.key_benign_inputs in analysis_output:
                for benign_input_info in analysis_output[self.key_benign_inputs]:
                    p = join(
                        dir_setup or dir_info["local"]["setup"],
                        str(benign_input_info["dir"]),
                    )
                    if os.path.exists(p):
                        beningn_input_count += len(os.listdir(p))
                    else:
                        self.emit_warning(
                            f"Path for benign test list {p} does not exist"
                        )

        self.stats.composite_stats.test_distribution[key] = (
            beningn_input_count,
            exploit_input_count,
        )

    def error_callback_handler(self, e: BaseException) -> None:
        self.emit_error("I got an exception!")
        self.emit_error(e)
        tb = traceback.format_tb(e.__traceback__)
        for l in tb:
            self.emit_error(l)
        self.stats.error_stats.is_error = True

    def watcher(self) -> None:
        event_handler = FileCreationHandler(self.message_queue)
        self.emit_highlight("Observing {}".format(self.root_artifact_dir))
        self.observer.schedule(
            event_handler, self.root_artifact_dir, recursive=True
        )  # type:ignore
        self.observer.start()  # type:ignore

        try:
            while self.observer.is_alive():
                self.observer.join(1)
        finally:
            self.observer.stop()  # type:ignore
            self.observer.join()

    def pre_process_event(self, event: FileSystemEvent) -> bool:
        if self.filter_event(event):
            # self.emit_debug("Is new file? {}".format(new_file))
            time.sleep(0.5)  # HACK: make sure file is written to
            return True
        # self.emit_debug("Filtered {}".format(event))
        return False

    def filter_event(self, event: FileSystemEvent) -> bool:
        """
        Exclude commonly known files which are not a signal for an interesting change.
        Directories are ignored!
        """
        if event.is_directory:
            return False
        if (
            ".state" in event.src_path
            or ".log" in event.src_path
            or ".trace" in event.src_path
            or ".bin" in event.src_path
            or ".dot" in event.src_path
            or "/backup/" in event.src_path
        ):
            return False
        if basename(event.src_path) in [
            "README.txt",
            "fuzz_bitmap",
            ".cur_input",
            ".affinity",
            ".affinity_lock",
            "plot_data",
            ".synced",
            ".state",
            "cmdline",
            "trace.sh",
            ".fuzzer_stats_tmp",
            definitions.INTERNAL_METADATA_JSON,
        ] or os.path.basename(os.path.normpath(dirname(event.src_path))) in [
            "benign_tests",
            "queue",
            "seeds",
        ]:
            return False
        return True

    def process_event(self, event: FileSystemEvent) -> None:
        # self.emit_debug(f"Processing! {event}")
        if basename(event.src_path) == self.exit_message:
            for _ in range(self.file_processor_count):
                self.emit_debug("Time to die")
                self.message_queue.put(self.exit_message)

        if basename(event.src_path) == "meta-data.json":
            for type, sub_root, handler in [
                ("Validate", self.validate_root, self.on_validation_finished),
                ("Repair", self.repair_root, self.on_repair_finished),
                ("Localize", self.localize_root, self.on_localization_finished),
                ("Analyze", self.analyze_root, self.on_analysis_finished),
                ("Select", self.select_root, self.on_selection_finished),
                (
                    "IterativeRepair",
                    self.iterative_repair_root,
                    self.on_repair_finished,
                ),
                ("Bisect", self.bisect_root, self.on_bisection_finished),
            ]:
                if event.src_path.startswith(sub_root):
                    self.emit_highlight("{} update".format(type))
                    handler(event)
                    break
        else:
            if event.src_path.startswith(self.fuzz_root):
                # self.emit_highlight("Fuzz Update")
                # self.emit_debug(dirname(event.src_path))
                if dirname(event.src_path).endswith("crashes"):
                    # self.emit_normal("Found a crash!")
                    self.task_pool.apply_async(
                        self.on_crash_found,
                        [event],
                        error_callback=self.error_callback_handler,
                    )
            # elif (
            #     os.path.commonprefix([event.src_path, self.crash_analyze_root])
            #     == self.crash_analyze_root
            # ):
            #    pass
            # else:
            # self.emit_debug("Ignoring file {}".format(event.src_path))
            #    pass
            # elif (
            #     os.path.commonprefix(
            #         [event.src_path, self.crash_analyze_root]
            #     )
            #     == list(self.task_mappings["crash-analyze"].keys())[0]
            # ):
            #     # self.emit_debug("Ignoring crash analysis update")
            #     pass

    def on_fuzzing_finished(self, base_dir: str) -> None:
        try:
            resulting_artefacts = os.listdir(base_dir)
            if len(resulting_artefacts) == 0:
                self.emit_warning(
                    "No results found when fuzzing finishes! Surely an error"
                )
                self.stats.error_stats.is_error = True
                return

            benign_dir = join(base_dir, "benign_tests")
            crash_dir = join(base_dir, "crashing_tests")

            subtask_hash = hashlib.sha256()
            subtask_hash.update(str(time.time()).encode("utf-8"))
            subtask_tag = subtask_hash.hexdigest()[: values.hash_suffix_length]

            self.emit_debug(f"Base dir is {base_dir}")
            (base_setup, enhanced_setup) = self.get_setup_directories(
                base_dir, subtask_tag
            )

            # self.emit_debug(f"Setup dir is {base_setup}")
            # self.emit_debug(f"New setup dir is {enhanced_setup}")

            try:
                shutil.copytree(base_setup, enhanced_setup, dirs_exist_ok=True)
            except Exception as e:
                self.emit_warning(e)
                traceback.print_exc()

            os.makedirs(join(enhanced_setup, "benign_tests"), exist_ok=True)
            os.makedirs(join(enhanced_setup, "crashing_tests"), exist_ok=True)

            self.copy_tests(
                crash_dir,
                enhanced_setup,
                "crashing_tests",
                self.task_config_info.get(
                    definitions.KEY_CONFIG_FAILING_TEST_COUNT, -1
                ),
            )

            self.copy_tests(
                benign_dir,
                enhanced_setup,
                "benign_tests",
                self.task_config_info.get(
                    definitions.KEY_CONFIG_PASSING_TEST_COUNT, -1
                ),
            )

            self.emit_debug(
                f"Looking for! {join(base_dir,definitions.INTERNAL_METADATA_JSON)}"
            )
            internal_data = reader.read_json(
                join(base_dir, definitions.INTERNAL_METADATA_JSON)
            )
            if not internal_data:
                self.error_exit(
                    "How did it finish but the internal file was not generated??"
                )

            old_bug_info = internal_data["bug_info"]

            bug_info_extension = reader.read_json(join(base_dir, "meta-data.json"))
            if bug_info_extension is None:
                self.emit_error("Could not find meta-data.json")

            new_bug_info = self.merge_dict(
                old_bug_info,
                cast(
                    Dict[Any, Any],
                    (
                        bug_info_extension[0]
                        if isinstance(bug_info_extension, list)
                        else bug_info_extension
                    ),
                ),
            )

            writer.write_as_json(
                new_bug_info,
                join(
                    list(self.root_task_mappings["fuzz"].keys())[0],
                    f"meta-data-{subtask_tag}.json",
                ),
            )

            if len(os.listdir(join(enhanced_setup, "crashing_tests"))) == 0:
                self.emit_warning(
                    "Could not find a crashing test for {} {}. Terminating path.".format(
                        self.bug_info[self.key_subject], self.bug_info[self.key_bug_id]
                    )
                )
            else:
                self.do_step(
                    new_bug_info,
                    subtask_hash,
                    subtask_tag,
                    ["crash-analyze", "localize", "repair"],
                    internal_data["path"],
                )

        except Exception as e:
            self.emit_warning(e)
            traceback.print_exc()
        pass

    def on_crash_found(self, event: FileSystemEvent) -> None:
        try:
            crash_dir = dirname(event.src_path)
            benign_dir = join(dirname(crash_dir), "queue")
            current_time = int(time.time())

            if self.last_crash is not None and current_time - self.last_crash <= (
                2 if self.cpu_count >= 16 else 14
            ):
                # self.emit_debug("Debouncing the crash")
                return
            # self.emit_debug("Crash found! {}".format(event))

            self.last_crash = int(time.time())

            subtask_hash = hashlib.sha256()
            subtask_hash.update(str(time.time()).encode("utf-8"))
            subtask_tag = subtask_hash.hexdigest()[: values.hash_suffix_length]

            # Assumption - the fuzzer is at the start of the chain, therefore I can take this directly from the proto args
            base_setup = self.proto_args[0]["local"]["setup"]
            # self.emit_debug(f"Base setup dir is {base_setup}")
            enhanced_setup = join(
                self.root_setups_dir,
                f"{basename(os.path.normpath(base_setup))}-{subtask_tag}",
            )
            # self.emit_debug(f"New setup dir is {enhanced_setup}")

            try:
                shutil.copytree(base_setup, enhanced_setup, dirs_exist_ok=True)
            except Exception as e:
                self.emit_warning(e)
                traceback.print_exc()

            os.makedirs(join(enhanced_setup, "benign_tests"), exist_ok=True)
            os.makedirs(join(enhanced_setup, "crashing_tests"), exist_ok=True)

            shutil.copy(event.src_path, join(enhanced_setup, "crashing_tests", ""))
            self.copy_tests(
                benign_dir,
                enhanced_setup,
                "benign_tests",
                self.task_config_info.get(
                    definitions.KEY_CONFIG_PASSING_TEST_COUNT, -1
                ),
            )

            new_bug_info = deepcopy(self.bug_info)

            new_bug_info[self.key_analysis_output] = [
                {
                    "generator": "Crash reaction",
                    "confidence": 1.0,
                    self.key_exploit_inputs: [
                        {"format": "raw", "dir": "crashing_tests"}
                    ],
                    self.key_benign_inputs: [{"format": "raw", "dir": "benign_tests"}],
                }
            ]
            new_bug_info["test_dir_abspath"] = self.dir_setup

            writer.write_as_json(
                new_bug_info,
                join(
                    list(self.root_task_mappings["fuzz"].keys())[0],
                    f"meta-data-{subtask_tag}.json",
                ),
            )

            self.do_step(
                new_bug_info,
                subtask_hash,
                subtask_tag,
                ["crash-analyze", "localize", "repair"],
                [],
            )
        except Exception as e:
            self.emit_warning(e)
            traceback.print_exc()
        pass

    def on_crash_analysis_finished(self, base_dir: str) -> None:
        try:
            # self.emit_debug(
            #    f"Looking for! {join(base_dir, definitions.INTERNAL_METADATA_JSON)}"
            # )
            internal_data = reader.read_json(
                join(base_dir, definitions.INTERNAL_METADATA_JSON)
            )
            if not internal_data:
                self.error_exit(
                    "How did it finish but the internal file was not generated??"
                )

            old_bug_info = internal_data["bug_info"]
            bug_info_extension = reader.read_json(join(base_dir, "meta-data.json"))
            if bug_info_extension is None:
                self.emit_error("Could not find meta-data.json")

            new_bug_info = self.merge_dict(
                old_bug_info,
                cast(
                    Dict[Any, Any],
                    (
                        bug_info_extension[0]
                        if isinstance(bug_info_extension, list)
                        else bug_info_extension
                    ),
                ),
            )

            # self.emit_error("Base dir is {}".format(base_dir))
            resulting_artefacts = os.listdir(base_dir)
            if len(resulting_artefacts) == 0 or resulting_artefacts == [base_dir]:
                self.emit_warning("No resulting artifacts found! Surely an error")
                self.stats.error_stats.is_error = True
                return

            if (
                "triggered_sanitizer" not in new_bug_info
                or new_bug_info["triggered_sanitizer"] == "NAN"
            ):
                self.emit_warning("No triggered possible sanitizer. Ignoring")
                return

            crash_signature = " ".join(
                map(
                    str,
                    zip(
                        new_bug_info[definitions.KEY_TIEBREAKER_FUNCTIONS],
                        new_bug_info[definitions.KEY_TIEBREAKER_FILES],
                    ),
                )
            )
            self.emit_debug(f"Created crash signature -- {crash_signature} --")
            if crash_signature in self.crash_signature_set:
                self.emit_normal("Crash was evaluated successfully before, terminating")
                return

            benign_dir = join(base_dir, "benign_tests")
            crash_dir = join(base_dir, "crashing_tests")

            subtask_hash = hashlib.sha256()
            subtask_hash.update(str(time.time()).encode("utf-8"))
            subtask_tag = subtask_hash.hexdigest()[: values.hash_suffix_length]

            (base_setup, enhanced_setup) = self.get_setup_directories(
                base_dir, subtask_tag
            )

            # self.emit_debug(f"Setup dir is {base_setup}")
            # self.emit_debug(f"New setup dir is {enhanced_setup}")

            try:
                shutil.copytree(
                    base_setup,
                    enhanced_setup,
                    dirs_exist_ok=True,  # Unsafe - , ignore=shutil.ignore_patterns("core.[0-9]*")
                )
            except Exception as e:
                self.emit_error(f"exception while copying: {e}")

            os.makedirs(join(enhanced_setup, "benign_tests"), exist_ok=True)
            os.makedirs(join(enhanced_setup, "crashing_tests"), exist_ok=True)

            self.copy_tests(
                crash_dir,
                enhanced_setup,
                "crashing_tests",
                self.task_config_info.get(
                    definitions.KEY_CONFIG_FAILING_TEST_COUNT, -1
                ),
            )
            self.copy_tests(
                benign_dir,
                enhanced_setup,
                "benign_tests",
                self.task_config_info.get(
                    definitions.KEY_CONFIG_PASSING_TEST_COUNT, -1
                ),
            )

            writer.write_as_json(
                new_bug_info,
                join(
                    list(self.root_task_mappings["crash-analyze"].keys())[0],
                    f"meta-data-{subtask_tag}.json",
                ),
            )

            self.do_step(
                new_bug_info,
                subtask_hash,
                subtask_tag,
                ["bisect", "localize", "repair"],
                internal_data["path"],
            )
        except Exception as e:
            self.emit_warning(e)
            traceback.print_exc()
        pass

    def on_analysis_finished(self, event: FileSystemEvent) -> None:
        self.on_task_finished(event, ["fuzz", "crash-analyze", "localize", "repair"])

    def on_localization_finished(self, event: FileSystemEvent) -> None:
        self.on_task_finished(event, ["repair"])

    def on_repair_finished(self, event: FileSystemEvent) -> None:
        def copy_patches(
            base_setup: str, enhanced_setup: str, new_bug_info: Dict[str, Any]
        ) -> None:
            tool_name = new_bug_info[self.key_tool_name]
            os.makedirs(join(enhanced_setup, "patches", tool_name), exist_ok=True)
            self.emit_debug(
                f"Copying patches from {dirname(event.src_path)} to {enhanced_setup}"
            )
            # Inject new testcases

            # self.copy_tests(None, enhanced_setup, "crashing_tests", 20)
            # self.copy_tests(None, enhanced_setup, "benign_tests", 20)

            if os.path.exists(join(dirname(event.src_path), "patches")):
                shutil.copytree(
                    join(dirname(event.src_path), "patches"),
                    join(enhanced_setup, "patches", tool_name),
                    dirs_exist_ok=True,
                )
            # shutil.copy(event.src_path, join(enhanced_setup, "patches"))

        self.on_task_finished(event, ["validate"], copy_patches)

    # TODO implement map
    patch_validation_map: Dict[str, Tuple[LockType, bool]]
    vulnerability_validation_map: Dict[str, Tuple[LockType, bool]]

    def on_validation_finished(self, event: FileSystemEvent) -> None:
        self.emit_highlight("Validation finished")

        internal_data = self.read_json(
            join(dirname(event.src_path), definitions.INTERNAL_METADATA_JSON)
        )

        if not internal_data:
            self.error_exit("Something messed up")

        validation_output = self.read_json(event.src_path)
        validation_result = []
        if isinstance(validation_output, List):
            validation_result = validation_output[0]["validation_output"]
        patch_info: list[list[str]] = validation_result[0]["validation_result"]

        dir_info = internal_data["dir_info"]
        bug_info = internal_data["bug_info"]
        patch_dir = dir_info["local"]["patches"]
        vulnerability_id = bug_info[definitions.KEY_BUG_ID]
        patch_list = bug_info["patches"]
        generator = ""
        if patch_list:
            p_obj = patch_list[0]
            generator = p_obj.get("generator")
        retry_id = (vulnerability_id, generator)
        plausible_patches = []
        for patch_name, patch_class in patch_info:
            if patch_class.startswith("pass"):
                plausible_patches.append(join(patch_dir, *patch_name.split(":")))

        if len(plausible_patches) < 1:
            with self.repair_retry_map_lock:
                if retry_id not in self.repair_retry_map:
                    self.repair_retry_map[retry_id] = (Lock(), 0)

            retry_count = 0
            with self.repair_retry_map[retry_id][0]:
                retry_count = self.repair_retry_map[retry_id][1] + 1
                with self.repair_retry_map_lock:
                    self.repair_retry_map[retry_id] = (
                        self.repair_retry_map[retry_id][0],
                        retry_count,
                    )
                self.emit_warning(f"No plausible patch found!")

            if retry_count <= self.max_retry_count:
                self.emit_warning(
                    f"setting up retry for repair. Retry Count: {retry_count}"
                )
                self.on_task_finished(event, ["iterative-repair"])
                return
            else:
                self.emit_warning(
                    f"maximum retry count reached for repair tool:{generator}, will not continue"
                )
                self.clear_storage(internal_data, dir_info, bug_info)
                return

        with self.patch_validation_map_lock:
            if vulnerability_id not in self.patch_validation_map:
                self.patch_validation_map[vulnerability_id] = (Lock(), False)

            if self.patch_validation_map[vulnerability_id][1]:
                self.emit_warning(f"Already submitted a patch for {vulnerability_id}")
                self.clear_storage(internal_data, dir_info, bug_info)
                return

        self.clear_storage(internal_data, dir_info, bug_info)

    def clear_storage(self, internal_data, dir_info, bug_info):
        if values.use_purge:
            workflow_path = internal_data["path"]
            self.emit_normal(
                f"Clearing up copied files for path {','.join(workflow_path)}"
            )
            setup_dir = os.path.dirname(dir_info["local"]["setup"])
            log_dir = os.path.dirname(dir_info["local"]["logs"])
            master_setup_dir = os.path.dirname(setup_dir)
            master_log_dir = os.path.dirname(log_dir)
            for path_id in workflow_path:
                if path_id == "":
                    continue
                try:
                    setup_dir_path = (
                        f"{master_setup_dir}/{bug_info['bug_id']}-{path_id}"
                    )
                    log_dir_path = f"{master_log_dir}/{bug_info['bug_id']}-{path_id}"
                    experiment_dir_search = self.list_dir(
                        values.dir_experiments, f"*{path_id}"
                    )
                    if os.path.isdir(setup_dir_path):
                        shutil.rmtree(setup_dir_path)
                        # self.emit_normal(f"deleted path {setup_dir_path}")
                    if os.path.isdir(log_dir_path):
                        shutil.rmtree(log_dir_path)
                        # self.emit_normal(f"deleted path {log_dir_path}")
                    if experiment_dir_search:
                        expr_dir_path = experiment_dir_search[0]
                        if os.path.isdir(expr_dir_path):
                            shutil.rmtree(expr_dir_path)
                            # self.emit_normal(f"deleted path {expr_dir_path}")
                except Exception as e:
                    self.emit_error(f"error deleting path {path_id}: {e}")

    def on_selection_finished(self, event: FileSystemEvent) -> None:
        self.emit_highlight("Selection finished")
        self.emit_normal("The workflow has finished for this path.")
        #  self.on_task_finished(event, [])
        pass

    def on_bisection_finished(self, event: FileSystemEvent) -> None:
        self.emit_highlight("Bisection finished {}".format(event))

        internal_data = self.read_json(
            join(dirname(event.src_path), definitions.INTERNAL_METADATA_JSON)
        )

        if not internal_data:
            self.error_exit("Something messed up")

        dir_info = internal_data["dir_info"]
        bug_info = internal_data["bug_info"]
        # self.emit_debug(bug_info)
        exp_dir = dir_info["local"]["experiment"]
        sanitizer = bug_info["triggered_sanitizer"]["id"]
        harness = bug_info["harnesses"][0]
        commit = self.read_json(event.src_path)[0]["commit"].strip()

        failure_signature = commit

        failing_test = ""
        for analysis_output in bug_info["analysis_output"]:
            for exploit_inpus in analysis_output["exploit_inputs"]:
                if exploit_inpus["format"] == "raw":
                    for input_file in os.listdir(
                        os.path.join(dir_info["local"]["setup"], exploit_inpus["dir"])
                    ):
                        failing_test = join(
                            dir_info["local"]["setup"], exploit_inpus["dir"], input_file
                        )
        self.emit_debug(failing_test)

        self.emit_debug(f"Preparing to validate for {failure_signature}")

        with self.vulnerability_validation_map_lock:
            if failure_signature not in self.vulnerability_validation_map:
                self.vulnerability_validation_map[failure_signature] = (Lock(), False)

            if self.vulnerability_validation_map[failure_signature][1]:
                self.emit_warning(f"Already found a successful crash for {commit}")
                self.clear_storage(internal_data, dir_info, bug_info)
                return

        with self.vulnerability_validation_map[failure_signature][0]:
            found_new_vulnerability = True
            if found_new_vulnerability:
                with self.vulnerability_validation_map_lock:
                    self.vulnerability_validation_map[failure_signature] = (
                        self.vulnerability_validation_map[failure_signature][0],
                        True,
                    )

                crash_signature = " ".join(
                    map(
                        str,
                        zip(
                            bug_info[definitions.KEY_TIEBREAKER_FUNCTIONS],
                            bug_info[definitions.KEY_TIEBREAKER_FILES],
                        ),
                    )
                )
                self.crash_signature_set.add(crash_signature)

                self.on_task_finished(event, ["localize", "repair"])
            else:
                self.emit_warning(
                    "Vulnerability submission was not successful. Please check why"
                )

        self.clear_storage(internal_data, dir_info, bug_info)

    def validate_metadata(self, metadata: List[Dict[str, Any]]) -> None:
        validator = Draft7Validator(general_section_schema)
        errors = list(validator.iter_errors(metadata))
        if len(errors) != 0:
            for error in errors:
                self.emit_warning(error.message)
                self.emit_warning(error.path)
            raise ValueError("Metadata is not valid. Will not continue")

    def on_task_finished(
        self,
        event: FileSystemEvent,
        next_task_options: List[CompositeTaskType],
        on_copy: Optional[Callable[[str, str, Dict[str, Any]], None]] = None,
    ) -> None:
        """
        Generic method for handling the completion of a task.
        On_copy is an entrypoint for addditional processing that can be done after the copy of the setup directory.
        The arguments for on_copy are the base_setup, enhanced_setup directories and the new_bug_info.
        """
        try:
            subtask_hash = hashlib.sha256()
            subtask_hash.update(str(time.time()).encode("utf-8"))
            subtask_tag = subtask_hash.hexdigest()[: values.hash_suffix_length]

            root_folder = os.path.dirname(event.src_path)
            # If a meta-data.json is created at composite-workspace/run-x/artifacts/tool/../meta-data.json
            # I want to access composite-workspace/run-x/artifacts/tool/cerberus-internal
            while (
                os.path.dirname(os.path.dirname(root_folder)) != self.root_artifact_dir
            ):
                root_folder = os.path.dirname(root_folder)

            (base_setup, enhanced_setup) = self.get_setup_directories(
                root_folder, subtask_tag
            )

            # self.emit_debug(f"Setup dir is {base_setup}")
            # self.emit_debug(f"New setup dir is {enhanced_setup}")

            try:
                shutil.copytree(base_setup, enhanced_setup, dirs_exist_ok=True)
            except Exception as e:
                self.emit_warning(e)
                traceback.print_exc()

            bug_info_extension = reader.read_json(event.src_path)
            if bug_info_extension is None:
                self.emit_error("Could not find meta-data.json")

            # self.emit_debug(
            #    f"Looking for! {join(root_folder,definitions.INTERNAL_METADATA_JSON)}"
            # )
            internal_data = reader.read_json(
                join(root_folder, definitions.INTERNAL_METADATA_JSON)
            )
            if not internal_data:
                self.error_exit(
                    "How did it finish but the internal file was not generated??"
                )

            old_bug_info = internal_data["bug_info"]

            new_bug_info = self.merge_dict(
                old_bug_info,
                cast(
                    Dict[Any, Any],
                    (
                        bug_info_extension[0]
                        if isinstance(bug_info_extension, list)
                        else bug_info_extension
                    ),
                ),
            )

            if on_copy:
                on_copy(base_setup, enhanced_setup, new_bug_info)

            # self.validate_metadata([new_bug_info])

            self.do_step(
                new_bug_info,
                subtask_hash,
                subtask_tag,
                next_task_options,
                internal_data["path"],
            )

        except Exception as e:
            self.stats.error_stats.is_error = True
            self.emit_warning(e)
            traceback.print_exc()
        pass

    def copy_tests(
        self, source_dir: str, destination_dir: str, subtype: str, limit: int
    ) -> None:
        os.makedirs(join(destination_dir, subtype, ""), exist_ok=True)
        if not os.path.exists(source_dir):
            return

        count = 0
        for test_case in os.listdir(source_dir):
            if test_case == "README.txt":
                continue
            if os.path.isdir(join(source_dir, test_case)):
                for test_name in os.listdir(join(source_dir, test_case)):
                    if os.path.isfile(
                        join(source_dir, test_case, test_name)
                    ) and not test_name.startswith("."):
                        shutil.copy(
                            join(source_dir, test_case, test_name),
                            join(destination_dir, subtype, ""),
                        )
                        count += 1
                        if limit != -1 and count >= limit:
                            break
            else:
                shutil.copy(
                    join(source_dir, test_case), join(destination_dir, subtype, "")
                )
                count += 1
            if limit != -1 and count >= limit:
                break

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        super().save_artifacts(dir_info)

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> CompositeToolStats:
        self.emit_normal("reading output")

        for _, status in self.stats.composite_stats.job_statuses.values():
            if status != TaskStatus.SUCCESS:
                self.stats.error_stats.is_error = True
                break

        return self.stats

    last_pool_print = time.time()

    def do_step(
        self,
        new_bug_info: Dict[str, Any],
        subtask_hash: Optional[Any],
        subtask_tag: Optional[str],
        next_task_options: List[CompositeTaskType],
        path: Optional[List[str]] = None,
    ) -> bool:
        """
        Start subsequent tasks in the workflow.
        Next_task_options is assumed to be a sorted list of the tasks that can be executed.
        Returns False if no tool was available for any of the possible follow-up tasks.
        """
        callbacks = {
            "fuzz": self.on_fuzzing_finished,
            "crash-analyze": self.on_crash_analysis_finished,
        }
        for next_task in next_task_options:
            if next_task in self.tool_map and self.tool_map[next_task]:
                for tool_constuctor, params, tag, type in self.tool_map[next_task]:
                    tool = tool_constuctor()

                    self.emit_debug(f"Allocating tool {tool.name} on pool default")

                    self.task_pool.apply_async(
                        self.run_subtask,
                        [
                            type,
                            *self.get_args(
                                tool,
                                tag,
                                new_bug_info,
                                subtask_hash,
                                subtask_tag or tag,
                                params,
                                new_timeout=(
                                    None if next_task != "crash-analyze" else (2 / 60.0)
                                ),
                                real_task_type=next_task,
                                task_type=type,
                            ),
                            path or list(),
                        ],
                        callback=callbacks.get(next_task, None),
                        error_callback=self.error_callback_handler,
                    )
                return True
        else:
            if path:
                self.stats.composite_stats.paths.append(path)
            self.emit_warning(
                "Did not find a successor task from the options {}. Terminating and saving this path.".format(
                    ",".join(next_task_options)
                )
            )
            return False

    def get_args(
        self,
        tool: AbstractTool,
        image_tag: str,
        new_bug_info: Optional[Dict[str, Any]] = None,
        new_hash: Optional[Any] = None,
        new_task_tag: Optional[str] = None,
        new_params: Optional[str] = None,
        new_timeout: Optional[float] = None,
        real_task_type: Optional[str] = None,
        task_type: Optional[str] = None,
    ) -> Tuple[
        DirectoryInfo,
        AbstractBenchmark,
        Dict[str, Any],
        Dict[str, Any],
        Dict[str, Any],
        str,
        str,
        AbstractTool,
    ]:
        """
        Construct the arguments for the run function from the proto_args.
        Certain arguments are replaceable.
        """
        (
            dir_info,
            benchmark,
            bug_info,
            task_config_info,
            container_config_info,
            run_index,
            hash,
        ) = self.proto_args

        if new_bug_info:
            bug_info = new_bug_info

        bug_info = copy.deepcopy(bug_info)  # Ensure bug info is unique

        if new_hash:
            hash = new_hash

        task_config_info_new = deepcopy(task_config_info)

        del task_config_info_new["container-id"]

        if image_tag:
            task_config_info_new[self.key_image_tag] = image_tag

        if new_task_tag:
            task_config_info_new[self.key_task_tag] = new_task_tag

        if new_params:
            task_config_info_new[definitions.KEY_TOOL_PARAMS] = new_params

        if new_timeout is not None:
            task_config_info_new[self.key_timeout] = new_timeout
            if task_type:
                task_config_info_new[task_type + "-" + self.key_timeout] = new_timeout

        if real_task_type:
            task_config_info_new[self.key_real_type] = real_task_type
            if new_timeout is not None:
                task_config_info_new[real_task_type + "-" + self.key_timeout] = (
                    new_timeout
                )

        bug_info[self.key_tool_name] = tool.name + (
            ("-" + tool.tool_tag) if tool.tool_tag else ""
        )
        return (
            dir_info,
            deepcopy(benchmark),
            bug_info,
            task_config_info_new,
            container_config_info,
            run_index,
            hash,
            tool,
        )

    def get_setup_directories(self, root: str, subtask_tag: str) -> Tuple[str, str]:
        """
        Extracts the setup directories from the internal representation or the proto arguments.
        """
        self.emit_debug("Root directory is {}".format(root))
        if os.path.isfile(join(root, definitions.INTERNAL_METADATA_JSON)):
            self.emit_debug("Found internal representation at {}".format(root))
            with open(join(root, definitions.INTERNAL_METADATA_JSON), "r") as f:
                data = json.loads(f.read())
                dir_info = data["dir_info"]
                # bug_info = data["bug_info"]
                base_setup = dir_info["local"]["setup"]
                previous_setup = basename(os.path.normpath(base_setup))
                if len(previous_setup.split("-")[-1]) == values.hash_suffix_length:
                    # The last argument is either the run index or the tool tag and for the run index to be reaching values.hash_suffix_length digits, that is suspicious
                    enhanced_setup = join(
                        self.root_setups_dir,
                        f"{previous_setup[:-(values.hash_suffix_length+1)]}-{subtask_tag}",
                    )
                else:
                    enhanced_setup = join(
                        self.root_setups_dir, f"{previous_setup}-{subtask_tag}"
                    )
        else:
            dir_info = self.proto_args[0]
            base_setup = dir_info["local"]["setup"]
            enhanced_setup = join(
                self.root_setups_dir,
                f"{basename(os.path.normpath(base_setup))}-{subtask_tag}",
            )
        return (base_setup, enhanced_setup)

    def make_root_task_mappings(
        self, root_dir: str
    ) -> Dict[CompositeTaskType, Dict[str, Dict[str, str]]]:
        """
        Create the mappings for each task type.
        When the tool is created we add this mapping to allow for a common output directory
        """
        task_mappings: Dict[CompositeTaskType, Dict[str, Dict[str, str]]] = {
            "fuzz": {join(root_dir, "fuzzing"): {"bind": "/output", "mode": "rw"}},
            "repair": {join(root_dir, "repair"): {"bind": "/output", "mode": "rw"}},
            "analyze": {join(root_dir, "analyze"): {"bind": "/output", "mode": "rw"}},
            "select": {join(root_dir, "select"): {"bind": "/output", "mode": "rw"}},
            "validate": {join(root_dir, "validate"): {"bind": "/output", "mode": "rw"}},
            "localize": {join(root_dir, "localize"): {"bind": "/output", "mode": "rw"}},
            "bisect": {join(root_dir, "bisect"): {"bind": "/output", "mode": "rw"}},
            "crash-analyze": {
                join(root_dir, "crash-analyze"): {"bind": "/output", "mode": "rw"}
            },
            "iterative-repair": {
                join(root_dir, "iterative-repair"): {"bind": "/output", "mode": "rw"}
            },
        }

        self.repair_root = list(task_mappings["repair"].keys())[0]
        self.analyze_root = list(task_mappings["analyze"].keys())[0]
        self.fuzz_root = list(task_mappings["fuzz"].keys())[0]
        self.select_root = list(task_mappings["select"].keys())[0]
        self.validate_root = list(task_mappings["validate"].keys())[0]
        self.localize_root = list(task_mappings["localize"].keys())[0]
        self.crash_analyze_root = list(task_mappings["crash-analyze"].keys())[0]
        self.iterative_repair_root = list(task_mappings["iterative-repair"].keys())[0]
        self.bisect_root = list(task_mappings["bisect"].keys())[0]

        # self.emit_debug(task_mappings)
        for task in task_mappings.values():
            for key in task.keys():
                os.makedirs(key, exist_ok=True)

        return task_mappings

    def make_task_mappings(
        self,
        tool_name: str,
        hash: str,
        root_mappings: Dict[CompositeTaskType, Dict[str, Dict[str, str]]],
        tool_tag: Optional[str] = None,
    ) -> Dict[CompositeTaskType, Dict[str, Dict[str, str]]]:
        res: Dict[CompositeTaskType, Dict[str, Dict[str, str]]] = {}
        for task_type, dir_mapping in root_mappings.items():
            new_mapping = {}
            for host_dir, container_dir_mapping in dir_mapping.items():
                new_mapping[
                    join(
                        host_dir,
                        (f"{tool_name}{ ('-' + tool_tag if tool_tag else '') }-{hash}"),
                    )
                ] = container_dir_mapping
            res[task_type] = new_mapping
        return res

    def event_worker(self) -> None:
        global active_jobs_lock  # Capture the process lock
        while True:
            event = self.message_queue.get()
            # self.emit_debug(f"Got message {event}")
            if isinstance(event, str):
                if event == self.exit_message:
                    if self.observer.is_alive():
                        self.observer.stop()  # type: ignore
                    break
                elif event == self.exit_message_delayed:
                    time.sleep(60)  # wait for 60 seconds
                    with (
                        active_jobs_lock
                    ):  # If no task started in the past minute, exit
                        if self.active_jobs == 0:
                            self.message_queue.put(self.exit_message)
                else:
                    self.emit_debug(f"Got string {event}. Why?")

                continue

            if (
                "crashes" in event.src_path
                and self.last_crash is not None
                and time.time() - self.last_crash <= (2 if self.cpu_count >= 16 else 14)
            ):
                # Short circuit to skip crashes
                continue

            if self.pre_process_event(event):
                # self.emit_debug("Got processed message {}".format(event))
                self.processed_file_pool.apply_async(self.handle_process_event, [event])

    def handle_process_event(self, event: FileSystemEvent):
        try:
            self.process_event(event)
        except Exception as e:
            print(f"Exception when processing {event}:\n {e}")
            tb = traceback.format_exc()
            self.emit_error(e)
            self.emit_error(tb)

    def merge_dict(
        self, info: Dict[Any, Any], candidate: Dict[Any, Any]
    ) -> Dict[Any, Any]:
        new_info = {}
        for key in info:
            new_info[key] = info[key]
            # Points of merging that are interesting are the keys
            if candidate and key in candidate and info[key] != candidate[key]:
                if type(info[key]) != type(candidate[key]):
                    self.emit_warning(
                        "Overriding key {} with value {} with value {}".format(
                            key, info[key], candidate[key]
                        )
                    )
                    new_info[key] = candidate[key]
                else:
                    if type(info[key]) != list and type(info[key]) != dict:
                        self.emit_warning(
                            "Overriding key {} with value {} with value {}".format(
                                key, info[key], candidate[key]
                            )
                        )
                        new_info[key] = candidate[key]
                    elif type(info[key]) == list:
                        new_info[key] = info[key] + candidate[key]
                    elif type(info[key]) == dict:
                        new_info[key] = self.merge_dict(info[key], candidate[key])
                    else:
                        self.emit_error("HOW?")
        if candidate:
            for key in candidate:
                if key not in info:
                    new_info[key] = candidate[key]

        return new_info
