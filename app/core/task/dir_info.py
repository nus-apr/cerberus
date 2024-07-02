import os
from os.path import join
from typing import Any
from typing import Dict
from typing import Optional
from typing import Tuple

from app.core import emitter
from app.core import values
from app.core.task.typing.DirectoryInfo import DirectoryInfo


def add_instrumentation_dir_info(
    dir_info: DirectoryInfo, tool_name: str
) -> DirectoryInfo:
    dir_info["local"]["instrumentation"] = join(
        dir_info["local"]["setup"], tool_name.lower()
    )
    dir_info["container"]["instrumentation"] = join(
        dir_info["container"]["setup"], tool_name.lower()
    )
    return dir_info


def generate_local_dir_info(
    benchmark_name: str,
    subject_name: str,
    bug_name: str,
    setup_dir_override: Optional[str],
    logs_dir_override: Optional[str] = None,
    artifacts_dir_override: Optional[str] = None,
    copy_experiment: Tuple[bool, str] = (False, ""),
) -> Dict[str, str]:
    dir_path = join(benchmark_name, subject_name, bug_name, "")
    dir_artifact_local = join(values.dir_artifacts, dir_path)

    if copy_experiment[0]:
        dir_exp_local = join(values.dir_experiments, copy_experiment[1], dir_path)
    else:
        dir_exp_local = join(values.dir_experiments, dir_path)

    dir_setup_local = join(values.dir_benchmark, dir_path)
    dir_logs_local = join(values.dir_logs, dir_path)

    if setup_dir_override and os.path.exists(setup_dir_override):
        dir_setup_local = setup_dir_override

    if logs_dir_override and os.path.exists(logs_dir_override):
        dir_logs_local = logs_dir_override

    if artifacts_dir_override and os.path.exists(artifacts_dir_override):
        dir_artifact_local = artifacts_dir_override

    dir_bugs_local = join(dir_setup_local, "bugs")
    dir_localization_local = join(dir_setup_local, "localization")
    dir_patches_local = join(dir_setup_local, "patches")
    dir_validation_local = join(dir_setup_local, "validation")
    dir_selection_local = join(dir_setup_local, "selection")

    dir_aux_local = join(values.dir_benchmark, benchmark_name, subject_name, ".aux")
    dir_base_local = join(values.dir_benchmark, benchmark_name, subject_name, "base")
    for directory in [
        dir_exp_local,
        dir_setup_local,
        dir_aux_local,
        dir_base_local,
        dir_bugs_local,
        dir_patches_local,
        dir_localization_local,
        dir_validation_local,
        dir_selection_local,
    ]:
        if not os.path.isdir(directory):
            os.makedirs(directory, exist_ok=True)

    return {
        "logs": dir_logs_local,
        "artifacts": dir_artifact_local,
        "experiment": dir_exp_local,
        "setup": dir_setup_local,
        "base": dir_base_local,
        "aux": dir_aux_local,
        "patches": dir_patches_local,
        "localization": dir_localization_local,
        "selection": dir_selection_local,
        "validation": dir_validation_local,
        "bugs": dir_bugs_local,
    }


def generate_local_tool_dir_info(
    benchmark_name: str,
    subject_name: str,
    bug_name: str,
    hash: Any,
    task_identifier: str,
    setup_dir_override: Optional[str],
    logs_dir_override: Optional[str] = None,
    artifacts_dir_override: Optional[str] = None,
    copy_experiment: bool = False,
) -> Dict[str, str]:
    dir_name = f"{task_identifier}-{hash.hexdigest()[:8]}"
    base_info = generate_local_dir_info(
        benchmark_name,
        subject_name,
        bug_name,
        setup_dir_override,
        logs_dir_override,
        artifacts_dir_override,
        (copy_experiment, dir_name),
    )

    dir_result_local = join(values.dir_results, dir_name)
    dir_logs_local = join(values.dir_logs, dir_name)
    dir_artifact_local = join(values.dir_artifacts, dir_name)

    if logs_dir_override and os.path.exists(logs_dir_override):
        dir_logs_local = logs_dir_override

    if artifacts_dir_override and os.path.exists(artifacts_dir_override):
        dir_artifact_local = artifacts_dir_override

    for directory in [dir_logs_local, dir_result_local, dir_artifact_local]:
        os.makedirs(directory, exist_ok=True)

    base_info["logs"] = dir_logs_local
    base_info["artifacts"] = dir_artifact_local
    base_info["results"] = dir_result_local

    return base_info


def generate_container_dir_info(
    benchmark_name: str, subject_name: str, bug_name: str
) -> Dict[str, str]:
    dir_path = join(benchmark_name, subject_name, bug_name, "")

    dir_setup_container = join("/setup", dir_path)
    dir_exp_container = join(values.container_base_experiment, dir_path)
    dir_logs_container = "/logs"
    dir_artifact_container = "/output"
    dir_aux_container = join(dir_exp_container, ".aux")
    dir_base_container = join(dir_exp_container, "base")

    return {
        "logs": dir_logs_container,
        "artifacts": dir_artifact_container,
        "experiment": dir_exp_container,
        "setup": dir_setup_container,
        "base": dir_base_container,
        "aux": dir_aux_container,
    }


def generate_tool_dir_info(
    benchmark_name: str,
    subject_name: str,
    bug_name: str,
    hash: Any,
    task_identifier: str,
    setup_dir_override: Optional[str],
    logs_dir_override: Optional[str] = None,
    artifacts_dir_override: Optional[str] = None,
    copy_experiment: bool = False,
) -> DirectoryInfo:
    dir_info: DirectoryInfo = {
        "local": generate_local_tool_dir_info(
            benchmark_name,
            subject_name,
            bug_name,
            hash,
            task_identifier,
            setup_dir_override,
            logs_dir_override,
            artifacts_dir_override,
            copy_experiment,
        ),
        "container": generate_container_dir_info(
            benchmark_name, subject_name, bug_name
        ),
    }
    return dir_info


def generate_dir_info(
    benchmark_name: str,
    subject_name: str,
    bug_name: str,
    setup_dir_override: Optional[str],
    logs_dir_override: Optional[str] = None,
) -> DirectoryInfo:
    dir_info: DirectoryInfo = {
        "local": generate_local_dir_info(
            benchmark_name,
            subject_name,
            bug_name,
            setup_dir_override,
            logs_dir_override,
        ),
        "container": generate_container_dir_info(
            benchmark_name, subject_name, bug_name
        ),
    }
    return dir_info
