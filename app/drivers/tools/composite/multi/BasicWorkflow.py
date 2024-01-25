import csv
import hashlib
import os
import shutil
import time
import traceback
from copy import deepcopy
from multiprocessing import Lock
from multiprocessing.pool import ThreadPool
from os.path import basename
from os.path import dirname
from os.path import join
from queue import Queue
from typing import Any
from typing import cast
from typing import Dict
from typing import List
from typing import Literal
from typing import Optional
from typing import Set
from typing import Tuple
from typing import Union

from watchdog.events import DirCreatedEvent
from watchdog.events import FileCreatedEvent
from watchdog.events import FileSystemEvent
from watchdog.events import FileSystemEventHandler
from watchdog.observers import Observer

from app.core import configuration
from app.core import definitions
from app.core import reader
from app.core import utilities
from app.core import values
from app.core import writer
from app.core.main import create_task_identifier
from app.core.main import create_task_image_identifier
from app.core.task import analyze
from app.core.task import fuzz
from app.core.task import repair
from app.core.task import select
from app.core.task import task
from app.core.task.typing.CompositeSequence import CompositeSequence
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.task.typing.TaskType import CompsiteTaskType
from app.core.task.typing.TaskType import TaskType
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.drivers.tools.composite.AbstractCompositeTool import AbstractCompositeTool
from app.drivers.tools.composite.multi.basic.FileCreationHandler import (
    FileCreationHandler,
)
from app.drivers.tools.MockTool import MockTool


class BasicWorkflow(AbstractCompositeTool):
    key_task_tag: str = "task_tag"
    key_image_tag: str = "image_tag"

    def __init__(self):
        self.name = basename(__file__)[:-3].lower()
        super().__init__(self.name)
        # preferably change to a container with the dependencies ready to reduce setup time
        self.image_name = "ubuntu:20.04"
        self.process_count = 12
        self.event_processor_count = 4
        self.exit_message = "quit"
        self.last_crash = 0

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
        """
        Entry point for the workflow.
        The function parses the composite sequence proivded in the composite_config_info
        and then starts an "initial tool" - fuzzer, localizer, repair tool, in that order of preference.
        Currently the system does not terminate a lot of things and this is left as a TODO
        """
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
        composite_config_info[self.key_make_metadata] = True
        composite_sequence = composite_config_info[self.key_composite_sequence]
        root_tool_tag = composite_config_info.get(definitions.KEY_TOOL_TAG, "")

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

        self.tool_map: Dict[
            CompsiteTaskType, List[Tuple[AbstractTool, str, str, str]]
        ] = {}

        for task_type, tools in composite_sequence.items():
            self.tool_map[task_type] = []
            for tool_info in tools:
                tag_fragments = []
                if root_tool_tag:
                    tag_fragments.append(root_tool_tag)

                tool_name = tool_info["name"]
                if tool_info.get("ignore", False):
                    self.emit_debug(f"Skip {tool_name}")
                    continue
                tool_params = tool_info.get(self.key_tool_params, "")

                extra_tool_tag = tool_info.get(definitions.KEY_TOOL_TAG, "")
                if extra_tool_tag:
                    tag_fragments.append(extra_tool_tag)

                tool_tag = "-".join(tag_fragments)

                real_type = tool_info.get(
                    "type", task_type
                )  # override the type when in "special" (crash-analyze) types
                if tool_name == "mock":
                    tool = cast(AbstractTool, MockTool())
                else:
                    tool = configuration.load_tool(tool_name, real_type)

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
                    bug_info,
                    tool_tag,
                )
                self.tool_map[task_type].append(
                    (tool, tool_params, tool_tag, real_type)
                )

        self.emit_highlight("Done with setup!")

        self.emit_highlight("Preparing watcher")
        watcher_handle = self.pool.apply_async(self.watcher)

        self.emit_highlight("Preparing workers")
        for _ in range(self.event_processor_count):
            self.pool.apply_async(self.event_worker)

        self.proto_args = (
            dir_info,
            benchmark,
            bug_info,
            composite_config_info,
            container_config_info,
            run_index,
            hash,
        )

        found_starter = False
        for starter in ["analyze", "fuzz", "crash-analyze", "repair"]:
            if starter in self.tool_map:
                found_starter = True
                for tool, params, tag, _ in self.tool_map[
                    cast(CompsiteTaskType, starter)
                ]:
                    self.pool.apply_async(
                        self.run_subtask,
                        [
                            starter,
                            *self.get_args(
                                tool, tag, new_params=params, new_task_tag=tag
                            ),
                        ],
                    )
                break

        if not found_starter:
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

    def run_subtask(
        self,
        task_type: TaskType,
        dir_info: DirectoryInfo,
        benchmark: AbstractBenchmark,
        bug_info,  # Entry from  meta-data.json
        composite_config_info,  # Task Profile
        container_config_info,  # Container Profile
        run_index,  # Specific iteration of the workflow run
        hash: Any,  # Hash, to be used for unique locations
        tool: AbstractTool,
    ):
        """
        Common entry point for a subtask, we take the original task tag to not create new images.
        This flow assumes that the run_composite function has prepared all the tags beforehand in order to quickly start new jobs.
        """
        try:
            values.task_type.set(task_type)
            values.current_task_profile_id.set(composite_config_info["id"])
            values.current_container_profile_id.set(composite_config_info["id"])
            tool_tag = composite_config_info.get(self.key_task_tag, "")
            image_tag = composite_config_info.get(self.key_image_tag, "")
            image_name = create_task_image_identifier(
                benchmark,
                tool,
                bug_info,
                image_tag,
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
                tool_tag,
            )
        except Exception as e:
            self.emit_warning(e)
            traceback.print_exc()

    def watcher(self):
        event_handler = FileCreationHandler(self.message_queue)
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
            # self.emit_debug("Did not filter {}".format(event))
            with self.mutex:
                if event.src_path not in self.observed:
                    self.observed.add(event.src_path)
                    new_file = True
                else:
                    new_file = False

            # self.emit_debug("Is new file? {}".format(new_file))
            if new_file:
                time.sleep(0.5)  # HACK: make sure file is written to
                return True
        # self.emit_debug("Filtered {}".format(event))
        return False

    def filter_event(self, event: FileSystemEvent):
        """
        Exclude commonly known files which are not a signal for an interesting change
        """
        if basename(event.src_path) in [
            "README.txt",
            "fuzz_bitmap",
            ".cur_input",
            ".affinity",
            ".affinity_lock",
            "plot_data",
            ".synced",
            "cmdline",
            ".fuzzer_stats_tmp",
        ]:
            return False
        if ".state" in event.src_path or ".trace" in event.src_path:
            return False
        return True

    def process_event(self, event: FileSystemEvent):
        # self.emit_debug(f"Processing! {event}")
        if basename(event.src_path) == "quit":
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
            # self.emit_highlight("Fuzz Update")
            # self.emit_debug(dirname(event.src_path))
            if dirname(event.src_path).endswith("crashes"):
                # self.emit_normal("Found a crash!")
                self.pool.apply_async(self.on_crash_found, [event])
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
                [event.src_path, list(self.task_mappings["crash-analyze"].keys())[0]]
            )
            == list(self.task_mappings["crash-analyze"].keys())[0]
        ):
            # self.emit_debug("Ignoring crash analysis update")
            pass
        elif (
            os.path.commonprefix(
                [event.src_path, list(self.task_mappings["localize"].keys())[0]]
            )
            == list(self.task_mappings["localize"].keys())[0]
        ):
            if (
                not dirname(event.src_path).endswith("failing_test_identifiers")
                and not dirname(event.src_path).endswith("passing_test_identifiers")
                and not event.is_directory
                and basename(event.src_path) == "meta-data.json"
            ):
                self.emit_highlight("Localize Update")
                self.emit_highlight(event)
                self.pool.apply_async(self.on_localization_created, [event])

    def event_worker(self):
        while True:
            event = self.message_queue.get()
            if isinstance(event, str) and event == self.exit_message:
                if self.observer.is_alive():
                    self.observer.stop()
                break
            elif isinstance(event, str):
                self.emit_debug(f"Got string {event}. Why?")
                continue
            if self.pre_process_event(event):
                # self.emit_debug("Got message {}".format(event))
                try:
                    self.process_event(event)
                except Exception as e:
                    print(f"Exception when processing {event}:\n {e}")

    def on_crash_found(self, event: FileSystemEvent):
        try:
            crash_dir = dirname(event.src_path)
            benign_dir = join(dirname(crash_dir), "queue")
            current_time = int(time.time())

            if self.last_crash is not None and current_time - self.last_crash <= 12000:
                # self.emit_debug("Debouncing the crash")
                return

            self.last_crash = int(time.time())

            subtask_hash = hashlib.sha1()
            subtask_hash.update(str(time.time()).encode("utf-8"))
            subtask_tag = subtask_hash.hexdigest()[:8]

            base_setup = self.proto_args[0]["local"]["setup"]
            self.emit_debug(f"Base setup dir is {base_setup}")
            enhanced_setup = join(
                dirname(os.path.normpath(base_setup)),
                f"{basename(os.path.normpath(base_setup))}-{subtask_tag}",
            )
            self.emit_debug(f"New setup dir is {enhanced_setup}")

            shutil.copytree(base_setup, enhanced_setup)
            os.makedirs(join(enhanced_setup, "benign_tests"), exist_ok=True)
            os.makedirs(join(enhanced_setup, "crashing_tests"), exist_ok=True)

            crashing_tests = [basename(event.src_path)]
            shutil.copy(
                join(crash_dir, basename(event.src_path)),
                join(enhanced_setup, "tests", ""),
            )
            shutil.copy(
                join(crash_dir, basename(event.src_path)),
                join(enhanced_setup, "crashing_tests", ""),
            )

            benign_tests = self.copy_tests(benign_dir, enhanced_setup, "benign_tests")

            new_testcases = (
                crashing_tests + benign_tests + os.listdir(join(base_setup, "tests"))
            )

            self.emit_debug(f"New testcases are {new_testcases}")

            new_bug_info = deepcopy(self.bug_info)

            new_bug_info[self.key_exploit_list] = list(
                set(new_bug_info[self.key_exploit_list] + new_testcases)
            )

            new_bug_info[self.key_exploit_inputs] = [
                {"format": "raw", "dir": "crashing_tests"}
            ]
            new_bug_info[self.key_benign_inputs] = [
                {"format": "raw", "dir": "benign_tests"}
            ]
            new_bug_info["test_dir_abspath"] = self.dir_setup

            new_bug_info[self.key_passing_test_identifiers] = (
                benign_tests + new_bug_info[self.key_passing_test_identifiers]
            )

            new_bug_info[self.key_failing_test_identifiers] = (
                crashing_tests + new_bug_info[self.key_failing_test_identifiers]
            )

            writer.write_as_json(
                new_bug_info,
                join(
                    list(self.task_mappings["fuzz"].keys())[0],
                    f"meta-data-{subtask_tag}.json",
                ),
            )

            if "crash-analyze" in self.tool_map:
                self.emit_debug("starting crash analyzer")
                for tool, params, tag, type in self.tool_map["crash-analyze"]:
                    self.emit_debug("with params {}".format(params))
                    self.pool.apply_async(
                        self.run_subtask,
                        [
                            type,
                            *self.get_args(
                                tool,
                                tag,
                                new_bug_info,
                                subtask_hash,
                                subtask_tag,
                                params,
                                (2 / 60.0),  # Run for 2 minutes
                            ),
                        ],
                        callback=self.on_crash_analysis_finished,
                    )
            elif "localize" in self.tool_map:
                self.emit_debug("starting localizer")
                for tool, params, tag, type in self.tool_map["localize"]:
                    self.emit_debug(f"tool! {tool.name}")
                    self.pool.apply_async(
                        self.run_subtask,
                        [
                            "localize",
                            *self.get_args(
                                tool,
                                tag,
                                new_bug_info,
                                subtask_hash,
                                subtask_tag,
                                params,
                            ),
                        ],
                    )

            elif "repair" in self.tool_map:
                self.emit_debug("starting repair")
                for tool, params, tag, type in self.tool_map["repair"]:
                    self.pool.apply_async(
                        self.run_subtask,
                        [
                            "repair",
                            *self.get_args(
                                tool,
                                tag,
                                new_bug_info,
                                subtask_hash,
                                subtask_tag,
                                params,
                            ),
                        ],
                    )
            else:
                self.emit_debug("What do I do??")
        except Exception as e:
            self.emit_warning(e)
            traceback.print_exc()
        pass

    def on_localization_created(self, event: FileSystemEvent):
        try:
            subtask_hash = hashlib.sha1()
            subtask_hash.update(str(time.time()).encode("utf-8"))
            subtask_tag = subtask_hash.hexdigest()[:8]

            base_setup = self.proto_args[0]["local"]["setup"]
            enhanced_setup = join(
                dirname(os.path.normpath(base_setup)),
                f"{basename(os.path.normpath(base_setup))}-{subtask_tag}",
            )
            self.emit_debug(f"Setup dir is {base_setup}")
            self.emit_debug(f"New setup dir is {enhanced_setup}")

            shutil.copytree(base_setup, enhanced_setup)

            self.emit_debug("Copying")

            new_bug_info = deepcopy(self.bug_info)

            bug_info_extension = reader.read_json(event.src_path)
            new_bug_info = dict(new_bug_info, **(bug_info_extension[0]))

            if "repair" in self.tool_map:
                for tool, params, tag, type in self.tool_map["repair"]:
                    self.pool.apply_async(
                        self.run_subtask,
                        [
                            "repair",
                            *self.get_args(
                                tool,
                                tag,
                                new_bug_info,
                                subtask_hash,
                                subtask_tag,
                                params,
                            ),
                        ],
                    )
        except Exception as e:
            self.emit_warning(e)
            traceback.print_exc()
        pass

    def on_crash_analysis_finished(self, res):
        try:
            base_dir = list(self.task_mappings["crash-analyze"].keys())[0]
            benign_dir = join(base_dir, "benign_tests")
            crash_dir = join(base_dir, "crashing_tests")

            subtask_hash = hashlib.sha1()
            subtask_hash.update(str(time.time()).encode("utf-8"))
            subtask_tag = subtask_hash.hexdigest()[:8]

            base_setup = self.proto_args[0]["local"]["setup"]
            self.emit_debug(f"Base setup dir is {base_setup}")
            enhanced_setup = join(
                dirname(os.path.normpath(base_setup)),
                f"{basename(os.path.normpath(base_setup))}-{subtask_tag}",
            )
            self.emit_debug(f"New setup dir is {enhanced_setup}")

            shutil.copytree(base_setup, enhanced_setup)
            os.makedirs(join(enhanced_setup, "benign_tests"), exist_ok=True)
            os.makedirs(join(enhanced_setup, "crashing_tests"), exist_ok=True)

            crashing_tests = self.copy_tests(
                crash_dir, enhanced_setup, "crashing_tests"
            )

            benign_tests = self.copy_tests(benign_dir, enhanced_setup, "benign_tests")

            new_testcases = (
                crashing_tests + benign_tests + os.listdir(join(base_setup, "tests"))
            )

            self.emit_debug(f"New testcases are {new_testcases}")

            new_bug_info = deepcopy(self.bug_info)

            bug_info_extension = reader.read_json(join(base_dir, "meta-data.json"))

            new_bug_info = dict(new_bug_info, **(bug_info_extension[0]))

            new_bug_info[self.key_exploit_list] = list(
                set(new_bug_info[self.key_exploit_list] + new_testcases)
            )

            new_bug_info[self.key_passing_test_identifiers] = (
                benign_tests + new_bug_info[self.key_passing_test_identifiers]
            )

            new_bug_info[self.key_failing_test_identifiers] = (
                crashing_tests + new_bug_info[self.key_failing_test_identifiers]
            )

            writer.write_as_json(
                new_bug_info,
                join(
                    list(self.task_mappings["fuzz"].keys())[0],
                    f"meta-data-{subtask_tag}.json",
                ),
            )

            if "localize" in self.tool_map:
                self.emit_debug("starting localizer")
                for tool, params, tag, type in self.tool_map["localize"]:
                    self.pool.apply_async(
                        self.run_subtask,
                        [
                            "localize",
                            *self.get_args(
                                tool,
                                tag,
                                new_bug_info,
                                subtask_hash,
                                subtask_tag,
                                params,
                            ),
                        ],
                    )

            elif "repair" in self.tool_map:
                self.emit_debug("starting repair")
                for tool, params, tag, type in self.tool_map["repair"]:
                    self.pool.apply_async(
                        self.run_subtask,
                        [
                            "repair",
                            *self.get_args(
                                tool,
                                tag,
                                new_bug_info,
                                subtask_hash,
                                subtask_tag,
                                params,
                            ),
                        ],
                    )
            else:
                self.emit_debug("What do I do??")

        except Exception as e:
            self.emit_warning(e)
            traceback.print_exc()
        pass

    def copy_tests(self, source_dir, destination_dir, subtype):
        tests = []
        for test_case in os.listdir(source_dir):
            if os.path.isdir(join(source_dir, test_case)) or test_case == "README.txt":
                tests.append(test_case)
                shutil.copy(
                    join(source_dir, test_case),
                    join(destination_dir, "tests", ""),
                )
                shutil.copy(
                    join(source_dir, test_case),
                    join(destination_dir, subtype, ""),
                )

        return tests

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

    def get_args(
        self,
        tool: AbstractTool,
        image_tag: str,
        new_bug_info: Optional[Dict[str, Any]] = None,
        new_hash: Optional[Any] = None,
        new_task_tag: Optional[str] = None,
        new_params: Optional[str] = None,
        new_timeout: Optional[float] = None,
    ):
        """
        Construct the arguments for the run function from the proto_args.
        Certain arguments are replaceable.
        """
        (
            dir_info,
            benchmark,
            bug_info,
            composite_config_info,
            container_config_info,
            run_index,
            hash,
        ) = self.proto_args

        if new_bug_info:
            bug_info = new_bug_info

        if new_hash:
            hash = new_hash

        composite_config_info_new = deepcopy(composite_config_info)

        del composite_config_info_new["container-id"]

        if image_tag:
            composite_config_info_new[self.key_image_tag] = image_tag

        if new_task_tag:
            composite_config_info_new[self.key_task_tag] = new_task_tag

        if new_params:
            composite_config_info_new[definitions.KEY_TOOL_PARAMS] = new_params

        if new_timeout is not None:
            composite_config_info_new[self.key_timeout] = new_timeout

        return (
            dir_info,
            benchmark,
            bug_info,
            composite_config_info_new,
            container_config_info,
            run_index,
            hash,
            tool,
        )

    def make_task_mappings(
        self, root_dir: str
    ) -> Dict[CompsiteTaskType, Dict[str, Dict[str, str]]]:
        """
        Create the mappings for each task type.
        When the tool is created we add this mapping to allow for a common output directory
        """
        task_mappings: Dict[CompsiteTaskType, Dict[str, Dict[str, str]]] = {
            "fuzz": {join(root_dir, "fuzzing"): {"bind": "/output", "mode": "rw"}},
            "repair": {join(root_dir, "repair"): {"bind": "/output", "mode": "rw"}},
            "analyze": {join(root_dir, "analyze"): {"bind": "/output", "mode": "rw"}},
            "select": {join(root_dir, "select"): {"bind": "/output", "mode": "rw"}},
            "validate": {join(root_dir, "validate"): {"bind": "/output", "mode": "rw"}},
            "localize": {join(root_dir, "localize"): {"bind": "/output", "mode": "rw"}},
            "crash-analyze": {
                join(root_dir, "crash-analyze"): {"bind": "/output", "mode": "rw"}
            },
        }
        self.emit_debug(task_mappings)
        for task in task_mappings.values():
            for key in task.keys():
                os.makedirs(key, exist_ok=True)

        return task_mappings
