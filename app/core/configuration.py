import json
import os
import sys

from app.core import values, emitter, utilities


def load_configuration_details(config_file_path):
    emitter.normal("loading profile setup")
    json_data = None
    if os.path.isfile(config_file_path):
        with open(config_file_path, "r") as conf_file:
            json_data = json.load(conf_file)
    else:
        utilities.error_exit("Configuration file does not exist")
    return json_data


def load_class(class_name):
    components = class_name.split(".")
    mod = __import__(components[0])
    for comp in components[1:]:
        mod = getattr(mod, comp)
    return mod


def load_tool(tool_name):
    emitter.normal("loading repair tool")
    class_file_path = values.dir_tool_drivers + tool_name + ".py"
    existing_tool_list = os.listdir(values.dir_tool_drivers)
    tool_class_name = None
    for tool in existing_tool_list:
        if tool.lower().replace(".py", "") == tool_name.lower():
            tool_class_name = tool.replace(".py", "")
    if not tool_class_name:
        utilities.error_exit("Unknown tool name", tool_name)
    mod = __import__("app.drivers.tools", fromlist=[tool_class_name])
    tool_class = getattr(mod, str(tool_class_name))
    initializer = getattr(tool_class, str(tool_class_name))
    return initializer()


def load_benchmark(benchmark_name):
    emitter.normal("loading benchmark")
    class_file_path = values.dir_benchmark_drivers + benchmark_name + ".py"
    existing_benchmark_list = os.listdir(values.dir_benchmark_drivers)
    benchmark_class_name = None
    for benchmark in existing_benchmark_list:
        if "Abstract" in benchmark or "init" in benchmark:
            continue
        if benchmark.lower().replace(".py", "") == benchmark_name.lower():
            benchmark_class_name = benchmark.replace(".py", "")
    if not benchmark_class_name:
        utilities.error_exit("Unknown benchmark name", benchmark_name)
    mod = __import__("app.drivers.benchmarks", fromlist=[benchmark_class_name])
    benchmark_class = getattr(mod, str(benchmark_class_name))
    initializer = getattr(benchmark_class, str(benchmark_class_name))
    return initializer()



class Configurations:
    __config_file = None
    __default_config_values = {
        "depth": 3,
        "iteration-limit": 1,
        "patch-rank-limit": 5,
        "stack-size": 15000,
        "time-duration": 60,  # minutes
        "use-cache": False,
        "use-container": True,
        "is-debug": False,
        "use-purge": False,
        "only-analyse": False,
        "only-setup": False,
        "rebuild-all": False,
        "rebuild-base": False,
        "subject-name": None,
        "benchmark-name": None,
        "dump-patches": False,
        "start-index": None,
        "end-index": None,
        "bug-id-list": [],
        "bug-index-list": [],
        "skip-index-list": [],
        "tool-list": [],
        "directories": {
            "data": "/data"
        }
    }
    __runtime_config_values = __default_config_values

    def convert_range(self, x):
        parts = x.split("-")
        if len(parts) == 1:
            return [int(parts[0])]
        if len(parts) == 0:
            return []
        parts[0] = 1 if parts[0] == "" else int(parts[0])
        parts[1] = 999 if parts[1] == "" else int(parts[1])
        return range(parts[0], parts[1] + 1)

    def read_arg_list(self, arg_list):
        emitter.normal("reading profile values")
        emitter.normal("reading configuration values from arguments")
        flat_map = lambda f, xs: (y for ys in xs for y in f(ys))
        self.__runtime_config_values["benchmark-name"] = arg_list.benchmark

        if arg_list.tool:
            self.__runtime_config_values["tool-list"] = [arg_list.tool]
        elif arg_list.tool_list:
            self.__runtime_config_values["tool-list"] = arg_list.tool_list

        if arg_list.subject:
            self.__runtime_config_values["subject-name"] = arg_list.subject

        if arg_list.tool_param:
            self.__runtime_config_values["tool-params"] = arg_list.tool_param

        if arg_list.rebuild_all:
            self.__runtime_config_values["rebuild-all"] = True

        if arg_list.rebuild_base:
            self.__runtime_config_values["rebuild-base"] = True

        if arg_list.debug:
            self.__runtime_config_values["is-debug"] = True
        if arg_list.config:
            self.__config_file = str(arg_list.config)
        if arg_list.cache:
            self.__runtime_config_values["use-cache"] = True
        if arg_list.purge:
            self.__runtime_config_values["use-purge"] = True
        if arg_list.only_analyse:
            self.__runtime_config_values["only-analyse"] = True
        if not arg_list.use_container or arg_list.use_local:
            self.__runtime_config_values["use-container"] = False

        if arg_list.data_dir:
            self.__runtime_config_values["dir-data"] = arg_list.data_dir

        if arg_list.only_setup:
            self.__runtime_config_values["only-setup"] = True

        if arg_list.config_id_list:
            self.__runtime_config_values["config-id-list"] = arg_list.config_id_list

        if arg_list.bug_index:
            self.__runtime_config_values["bug-index-list"] = [arg_list.bug_index]
        if arg_list.bug_index_list:
            self.__runtime_config_values["bug-index-list"] = flat_map(
                            self.convert_range,
                            str(arg_list.bug_index_list).split(","),
                        )

        if arg_list.bug_id:
            self.__runtime_config_values["bug-id-list"] = [arg_list.bug_id]
        if arg_list.bug_id_list:
            self.__runtime_config_values["bug-id-list"] = arg_list.bug_id_list.split(",")

        if arg_list.start_index:
            self.__runtime_config_values["start-index"] = int(arg_list.start_index)
        if arg_list.end_index:
            self.__runtime_config_values["end-index"] = int(arg_list.end_index)

        if arg_list.skip_index_list:
            self.__runtime_config_values["skip-index-list"] = str(arg_list.skip_index_list).split(",")


    def update_configuration(self):
        emitter.normal("updating configuration values")
        if not self.__runtime_config_values["only-setup"]:
            if not self.__runtime_config_values["tool-list"]:
                emitter.error("[invalid] --tool/-tool-list is missing")
                emitter.emit_help()
                exit(1)

        values.benchmark_name = self.__runtime_config_values["benchmark-name"]
        values.subject_name = self.__runtime_config_values["subject-name"]
        if values.subject_name:
            emitter.normal(
                "[info] running experiments for subject {}".format(values.subject_name)
            )
        values.file_meta_data = os.path.join(
            "benchmark", values.benchmark_name, "meta-data.json"
        )
        values.start_index = self.__runtime_config_values["start-index"]
        values.end_index = self.__runtime_config_values["end-index"]
        values.bug_index_list = self.__runtime_config_values["bug-index-list"]
        values.skip_index_list = self.__runtime_config_values["skip-index-list"]
        values.bug_id_list = self.__runtime_config_values["bug-id-list"]

        if (
                values.start_index is None
                and not values.bug_id_list is None
                and not values.bug_index_list
                and values.subject_name is None
        ):
            emitter.warning(
                "[warning] experiment id is not specified, running all experiments"
            )

        values.only_setup = self.__runtime_config_values["only-setup"]
        values.only_analyse = self.__runtime_config_values["only-analyse"]
        values.use_container = self.__runtime_config_values["use-container"]
        values.dump_patches = self.__runtime_config_values["dump-patches"]
        values.rebuild_all = self.__runtime_config_values["rebuild-all"]
        values.rebuild_base = self.__runtime_config_values["rebuild-base"]
        values.debug = self.__runtime_config_values["is-debug"]
        values.tool_list = self.__runtime_config_values["tool-list"]
        sys.setrecursionlimit(values.default_stack_size)
