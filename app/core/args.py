import argparse
import multiprocessing
from argparse import Action
from argparse import HelpFormatter
from argparse import Namespace
from operator import attrgetter
from typing import Iterable

from app.core import definitions
from app.core import utilities
from app.core import values


class SortingHelpFormatter(HelpFormatter):
    def add_arguments(self, actions: Iterable[Action]) -> None:
        actions = sorted(actions, key=attrgetter("option_strings"))
        super(SortingHelpFormatter, self).add_arguments(actions)


def parse_args() -> Namespace:
    parser = argparse.ArgumentParser(
        prog=values.tool_name,
        usage="%(prog)s [options]",
        formatter_class=SortingHelpFormatter,
    )
    parser._action_groups.pop()
    # required = parser.add_argument_group("Required arguments")

    optional = parser.add_argument_group("Optional arguments")

    optional.add_argument(
        definitions.ARG_TASK_TYPE,
        "-task",
        help="type of task to run {" + ",".join(values.get_task_types()) + "}",
        default=None,
        required=False,
        choices=values.get_task_types(),
        metavar="task_type",
    )

    optional.add_argument(
        definitions.ARG_TOOL_NAME,
        "-t",
        help="name of the repair/analysis tool\n\n"
        + ", ".join(values.get_list_tools()),
        choices=values.get_list_tools(),
        metavar="TOOL",
    )

    optional.add_argument(
        definitions.ARG_SUBJECT_BASED,
        "-sb",
        help="experiment image based on subject image\n\n",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_CONFIG_FILE, "-c", type=str, help="Path to the JSON config file"
    )

    optional.add_argument(
        definitions.ARG_PARALLEL,
        "-g",
        help="Activate Textual UI",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_SUBSEQUENCE,
        help="Use a subsequence of the composite workflow. Format is startInclusive-endInclusive",
    )

    optional.add_argument(
        definitions.ARG_BENCHMARK,
        "-b",
        help="program repair/analysis benchmark {"
        + ", ".join(values.get_list_benchmarks())
        + "}",
        choices=values.get_list_benchmarks(),
        metavar="",
    )
    optional.add_argument(
        definitions.ARG_DEBUG_MODE,
        "-d",
        help="print debugging information",
        action="store_true",
        default=False,
    )
    optional.add_argument(
        definitions.ARG_SECURE_HASH,
        help="activate secure hash checks",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_CACHE,
        help="use cached information for the process",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_BUG_INDEX, help="index of the bug in the benchmark", type=int
    )
    optional.add_argument(
        definitions.ARG_BUG_INDEX_LIST,
        "-l",
        help="list of bug indexes in the benchmark",
    )

    optional.add_argument(
        definitions.ARG_DOCKER_HOST,
        help="custom URL for the docker server which will host the containers",
    )

    optional.add_argument(
        definitions.KEY_TIMESTAMP,
        help="Add timestamp before every command",
        acton="store_true",
        default=False,
    )

    # TODO: Group list of tools based on type
    # group_tool = parser.add_argument_group(title='choice of tools')
    # repair_tools = parser.add_argument_group(title='repair tools')
    # analysis_tools = parser.add_argument_group(title='analysis tools')
    #
    # group_tool.add_argument(repair_tools)
    # group_tool.add_argument(analysis_tools)
    #
    # group.add_argument('bacon', help="Lovely bacon", action='none')
    # group.add_argument('egg', help="The runny kind", action='none')
    # group.add_argument('sausage', help="Just a roll", action='none')
    # group.add_argument('spam', help="Glorious SPAM", action='none')
    # group.add_argument('tomato', help="Sliced and diced", action='none')

    optional.add_argument(
        definitions.ARG_SUBJECT_NAME,
        "-s",
        help="filter the bugs using the subject name",
    )
    optional.add_argument(
        definitions.ARG_TOOL_PARAMS,
        "-p",
        help="pass parameters to the tool",
        default="",
    )
    optional.add_argument(
        definitions.ARG_TOOL_TAG,
        "-tt",
        help="append identifier to the tool name",
        default="",
    )
    optional.add_argument(
        definitions.ARG_TOOL_LIST,
        nargs="+",
        help="list of the repair/analysis tool {"
        + ", ".join(values.get_list_tools())
        + "}",
    )
    optional.add_argument(
        definitions.ARG_REBUILD_ALL_IMAGES,
        help="rebuild all images",
        action="store_true",
        default=False,
    )
    optional.add_argument(
        definitions.ARG_COMPACT_RESUTLS,
        help="compact results of runs - deletes artifacts after compressing",
        action="store_true",
        default=False,
    )
    optional.add_argument(
        definitions.ARG_REBUILD_BASE_IMAGE,
        help="rebuild the base images",
        action="store_true",
        default=False,
    )
    optional.add_argument(
        definitions.ARG_PURGE,
        help="clean everything after the experiment",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_ANALYSE_ONLY,
        help="analyse the experiment",
        action="store_true",
        default=False,
    )
    optional.add_argument(
        definitions.ARG_SETUP_ONLY,
        help="only setup the experiment",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_INSTRUMENT_ONLY,
        help="only instrument the experiment",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_RUN_TESTS_ONLY,
        help="only run the tests of the experiment",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_USE_SUBJECT_AS_BASE,
        help="use the subject image as the base image",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_USE_CONTAINER,
        help="use containers for experiments",
        dest="use_container",
        action="store_true",
        default=True,
    )

    optional.add_argument(
        definitions.ARG_USE_LATEST_IMAGE,
        help="pull latest image from Dockerhub",
        dest="use_latest_image",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_USE_LOCAL,
        help="use local machine for experiments",
        dest="use_local",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_DATA_PATH,
        help="directory path for data",
        dest="data_dir",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_TASK_PROFILE_ID_LIST,
        help="multiple list of task configuration profiles",
        dest="task_profile_id_list",
        nargs="+",
        default=[],
    )

    optional.add_argument(
        definitions.ARG_CONTAINER_PROFILE_ID_LIST,
        help="multiple list of container configuration profiles",
        dest="container_profile_id_list",
        nargs="+",
        default=[],
    )

    optional.add_argument(
        definitions.ARG_RUNS,
        help="number of runs for an experiment",
        type=int,
        default=1,
    )

    optional.add_argument(
        definitions.ARG_ALL_CPU_COUNT,
        help="max amount of CPU cores which can be used by Cerberus",
        type=int,
        default=max(1, multiprocessing.cpu_count() - 2),
    )

    optional.add_argument(
        definitions.ARG_ALL_GPU_COUNT,
        help="max amount of GPU cores which can be used by Cerberus",
        type=int,
        default=max(0, utilities.get_gpu_count()),
    )

    # optional.add_argument(
    #     definitions.ARG_TASK_CPU_COUNT,
    #     help="max amount of CPU cores which can be used by Cerberus per task",
    #     type=int,
    #     default=1,
    # )

    optional.add_argument(
        definitions.ARG_USE_GPU,
        help="allow gpu usage",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_SPECIAL_META, help="Special metadata file", default=""
    )

    optional.add_argument(definitions.ARG_BUG_ID, help="identifier of the bug")
    optional.add_argument(
        definitions.ARG_BUG_ID_LIST,
        help="list of identifiers for the bugs",
        nargs="+",
        default=[],
    )
    optional.add_argument(
        definitions.ARG_START_INDEX,
        help="starting index for the list of bugs",
        type=int,
    )
    optional.add_argument(
        definitions.ARG_END_INDEX, help="ending index for the list of bugs", type=int
    )
    optional.add_argument(
        definitions.ARG_SKIP_LIST,
        help="list of bug index to skip",
        type=str,
        default="",
    )
    args = parser.parse_args()
    return args
