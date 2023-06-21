import os
from os.path import join

from app.core.dirs.BaseDirsInfo import BaseDirsInfo


class Task:

    def __init__(self, task_config, base_dirs_info: BaseDirsInfo):

        self.task_config = task_config
        self.base_dirs_info = base_dirs_info

    def generate_local_dir_info(self, benchmark_name: str, subject_name: str, bug_name: str):
        dir_path = join(benchmark_name, subject_name, bug_name, "")
        dir_exp_local = join(self.base_dirs_info.get_experiments_dir(), dir_path)
        dir_setup_local = join(self.base_dirs_info.get_main_dir(), "benchmark", dir_path)
        dir_aux_local = join(self.base_dirs_info.get_benchmark_dir(), benchmark_name, subject_name, ".aux")
        dir_base_local = join(self.base_dirs_info.get_benchmark_dir(), benchmark_name, subject_name, "base")
        dir_logs_local = join(self.base_dirs_info.get_output_log_dir(), dir_path)
        dir_artifact_local = join(self.base_dirs_info.get_output_artifacts_dir(), dir_path)
        for directory in [dir_exp_local, dir_setup_local, dir_aux_local, dir_base_local]:
            if not os.path.isdir(directory):
                os.makedirs(directory, exist_ok=True)

        return {
            "logs": dir_logs_local,
            "artifacts": dir_artifact_local,
            "experiment": dir_exp_local,
            "setup": dir_setup_local,
            "base": dir_base_local,
            "aux": dir_aux_local,
        }

    def generate_local_tool_dir_info(self, benchmark_name: str, subject_name: str, bug_name: str, hash, tag_name: str):
        dir_name = f"{tag_name}-{hash.hexdigest()[:8]}"
        base_info = generate_local_dir_info(benchmark_name, subject_name, bug_name)

        dir_result_local = join(values.dir_results, dir_name)
        dir_log_local = join(values.dir_logs, dir_name)
        dir_artifact_local = join(values.dir_artifacts, dir_name)
        for directory in [dir_log_local, dir_result_local, dir_artifact_local]:
            os.makedirs(directory, exist_ok=True)

        base_info["logs"] = dir_log_local
        base_info["artifacts"] = dir_artifact_local
        base_info["results"] = dir_result_local

        return base_info

    def generate_container_dir_info(self, benchmark_name: str, subject_name: str, bug_name: str):
        dir_path = join(benchmark_name, subject_name, bug_name, "")

        dir_setup_container = join("/setup", dir_path)
        dir_exp_container = join("/experiment", dir_path)
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

    def generate_tool_dir_info(benchmark_name: str, subject_name: str, bug_name: str, hash, tag_name: str
    ) -> DirectoryInfo:
        dir_info: DirectoryInfo = {
            "local": generate_local_tool_dir_info(
                benchmark_name, subject_name, bug_name, hash, tag_name
            ),
            "container": generate_container_dir_info(
                benchmark_name, subject_name, bug_name
            ),
        }
        return dir_info

    def generate_dir_info(
            benchmark_name: str, subject_name: str, bug_name: str
    ) -> DirectoryInfo:
        dir_info: DirectoryInfo = {
            "local": generate_local_dir_info(benchmark_name, subject_name, bug_name),
            "container": generate_container_dir_info(
                benchmark_name, subject_name, bug_name
            ),
        }
        return dir_info
