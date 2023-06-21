from os.path import join

from app.core.dirs.task_dirs.TaskAbstractDirsInfo import TaskAbstractDirsInfo


class TaskLocalDirsInfo(TaskAbstractDirsInfo):

    def __init__(self, base_dirs_info, benchmark_name, bug_info):

        dir_path = join(benchmark_name, subject_name, bug_name, "")
        dir_exp = join(base_dirs_info.get_experiments_dir(), dir_path)
        dir_setup = join(base_dirs_info.get_main_dir(), "benchmark", dir_path)
        dir_aux = join(base_dirs_info.get_benchmark_dir(), benchmark_name, subject_name, ".aux")
        dir_base = join(base_dirs_info.get_benchmark_dir(), benchmark_name, subject_name, "base")
        dir_logs = join(base_dirs_info.get_output_log_dir(), dir_path)
        dir_artifact = join(base_dirs_info.get_output_artifacts_dir(), dir_path)

        super().__init__(dir_exp, dir_setup, dir_aux, dir_base, dir_logs, dir_artifact)
