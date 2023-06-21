from os.path import join

from app.core.dirs.BaseDirsInfo import BaseDirsInfo
from app.core.dirs.task_dirs.TaskAbstractDirsInfo import TaskAbstractDirsInfo


class TaskContainerDirsInfo(TaskAbstractDirsInfo):

    def __init__(self, benchmark_name, bug_info):

        dir_path = join(benchmark_name, subject_name, bug_name, "")
        dir_setup = join("/setup", dir_path)
        dir_exp = join("/experiment", dir_path)
        dir_logs = "/logs"
        dir_artifact = "/output"
        dir_aux = join(dir_exp, ".aux")
        dir_base = join(dir_exp, "base")

        super().__init__(dir_exp, dir_setup, dir_aux, dir_base, dir_logs, dir_artifact)
