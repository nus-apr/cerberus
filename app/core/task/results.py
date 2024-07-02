import hashlib
import os
import time
from os.path import join
from typing import Any
from typing import Dict

from app.core import definitions
from app.core import emitter
from app.core import logger
from app.core import utilities
from app.core import values
from app.core import writer
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.plugins import valkyrie


def collect_benchmark_result(
    bug_info: Dict[str, Any], benchmark: AbstractBenchmark
) -> None:
    emitter.normal("\t\t[framework] collecting benchmark results")
    hash = hashlib.sha1()
    hash.update(str(time.time()).encode("utf-8"))
    bug_id = str(bug_info[definitions.KEY_BUG_ID])
    subject_name = str(bug_info[definitions.KEY_SUBJECT])
    benchmark_tag_name = "{}-{}-{}-{}".format(
        benchmark.name, subject_name, bug_id, hash.hexdigest()[:8]
    )
    benchmark.print_stats()
    logger.log_benchmark_stats(benchmark_tag_name, benchmark.stats)
    construct_job_summary(
        benchmark_tag_name, values.dir_summaries_benchmarks, benchmark.stats.get_dict()
    )


def construct_job_summary(
    job_identifier: str, dir: str, results_summary: Dict[str, Any]
) -> str:
    json_f_name = f"experiment-summary-{job_identifier}.json"
    summary_f_path = join(dir, json_f_name)
    writer.write_as_json(results_summary, summary_f_path)
    return summary_f_path


def collect_tool_result(
    dir_info: DirectoryInfo, experiment_info: Dict[str, Any], tool: AbstractTool
) -> None:
    emitter.normal("\t\t[framework] collecting experiment results")
    task_tag_name = dir_info["local"]["logs"].split("/")[-1]
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    failing_test_identifiers_list = experiment_info.get(
        definitions.KEY_FAILING_TEST, []
    )
    tool.analyse_output(dir_info, bug_id, failing_test_identifiers_list)
    tool.print_stats()
    tool.save_trace()
    tool.log_output_path = ""
    logger.log_tool_stats(task_tag_name, tool.stats)
    dir_info["local"]["summary"] = construct_job_summary(
        task_tag_name, values.dir_summaries_tools, tool.stats.get_dict()
    )
    if values.use_valkyrie:
        patch_dir = join(dir_info["local"]["artifacts"], "patches")
        valkyrie.analyse_output(patch_dir, tool.stats)


def retrieve_results(archive_name: str, tool: AbstractTool) -> bool:
    emitter.normal("\t\tretrieving results")
    archive_path = join(values.dir_main, "results", tool.name.lower(), archive_name)
    if os.path.isfile(archive_path):
        extract_command = "cp {} {} ; ".format(archive_path, values.dir_results)
        extract_command += "cd {} ; ".format(values.dir_results)
        extract_command += "tar -xf {}" + archive_name
        utilities.execute_command(extract_command)
        return True
    else:
        emitter.error("\t\t[error] Result archive not found at {}".format(archive_path))
        return False


def save_artifacts(dir_info: DirectoryInfo, tool: AbstractTool) -> None:
    emitter.normal(
        "\t\t[framework] Saving artifacts from tool {}{} and cleaning up".format(
            tool.name, f"-{tool.tool_tag}" if tool.tool_tag else ""
        )
    )
    local_info = dir_info["local"]
    dir_results = local_info["results"]
    os.makedirs(dir_results, exist_ok=True)
    tool.save_artifacts(local_info)
    tool.post_process()
    save_command = "cp -f {} {} ; ".format(values.file_main_log, dir_results)
    save_command += "cp -f {}/* {}".format(values.file_error_log, dir_results)
    utilities.execute_command(save_command)
