import json
import os
from pathlib import Path
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class GRT5(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        # self.image_name = "grt5-dev"
        self.image_name = "xmcp/grt5:231029.1"
        self.hash_digest = (
            "sha256:a77d4e8a6d71cc41b7bda2b7e258e8956de0163789d6fbd730a983f75e8f2f21"
        )

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:

        self.timestamp_log_start()

        # print("!!! begin")
        # return #####

        assert bug_info["language"] == "java"
        assert len(bug_info[self.key_failing_test_identifiers]) > 0

        repo_path = (Path(self.dir_expr) / "src").resolve()
        setup_path = Path(self.dir_setup).resolve()
        # print(bug_info, task_config_info, self.container_id)

        # test list maybe `com.clz::mtd` or `com.clz`, let's make them into `com.clz`

        test_failed = []
        test_failed_set = set()
        for t in bug_info[self.key_failing_test_identifiers]:
            t = t.partition("::")[0]
        for t in bug_info[self.key_failing_test_identifiers]:
            t = t.partition("::")[0]
            if t not in test_failed_set:
                test_failed_set.add(t)
                test_failed.append(t)

        test_passed = []
        test_passed_set = set()
        for t in bug_info[self.key_passing_test_identifiers]:
            t = t.partition("::")[0]
            if t not in test_failed_set and t not in test_passed_set:
                test_passed_set.add(t)
                test_passed.append(t)

        self.write_json(
            {
                "id": int(bug_info["id"]),
                "repo_path": str(repo_path),
                "setup_script_path": str(setup_path),
                "sp_src": bug_info["source_directory"],
                "sp_test": bug_info["test_directory"],
                "tp_src": bug_info[self.key_dir_class],
                "tp_test": bug_info[self.key_dir_test_class],
                "cp_compile": ":".join(
                    [str(Path(self.dir_expr) / s) for s in bug_info["dependencies"]]
                ),
                "cp_test": ":".join(
                    [
                        str(repo_path / bug_info[self.key_dir_class]),
                        str(repo_path / bug_info["test_class_directory"]),
                        *[
                            str(Path(self.dir_expr) / s)
                            for s in bug_info["dependencies"]
                        ],
                    ]
                ),
                "lang_level": bug_info["java_version"],
                "test_passed": test_passed,
                "test_failed": test_failed,
                "test_timeout": bug_info["test_timeout"],
                "test_sh_fn": bug_info["test_script"],
                "total_timeout_s": int(float(task_config_info["timeout"]) * 3600),
                "cpus": task_config_info[self.key_cpus],
                "gpus": task_config_info[self.key_gpus],
            },
            "/root/workflow/info.json",
        )

        ret = self.run_command(
            'bash -c "python3 /root/workflow/main.py"',
            log_file_path="/root/workflow/log.txt",
        )

        # print(*self.read_file('/root/workflow/log.txt'), sep='')

        self.process_status(ret)
        self.timestamp_log_end()

        # print("!!! end")

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """

        self.run_command(f"cp -r /root/workflow/log.txt {self.dir_output}/")
        self.run_command(f"cp -r /root/workflow/fl {self.dir_output}/")
        self.run_command(f"cp -r /root/workflow/repair {self.dir_output}/")
        self.run_command(f"cp -r /root/workflow/patches {self.dir_output}/")
        super().save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self.stats.patches_stats.non_compilable
            self.stats.patches_stats.plausible
            self.stats.patches_stats.size
            self.stats.patches_stats.enumerations
            self.stats.patches_stats.generated

            self.stats.time_stats.total_validation
            self.stats.time_stats.total_build
            self.stats.time_stats.timestamp_compilation
            self.stats.time_stats.timestamp_validation
            self.stats.time_stats.timestamp_plausible
        """
        self.emit_normal("reading output")

        try:
            stats = self.read_json("/root/workflow/repair/stats.json")
        except Exception as e:
            print("cannot read stats", repr(e))
            stats = None

        if not stats:
            self.stats.error_stats.is_error = True
            return self.stats

        self.stats.patch_stats.size = stats["n_generated"]
        self.stats.patch_stats.enumerations = stats["n_validated"]
        self.stats.patch_stats.non_compilable = (
            stats["n_validated"] - stats["n_compilable"]
        )
        self.stats.patch_stats.plausible = stats["n_plausible"]
        self.stats.patch_stats.generated = min(5, stats["n_plausible"])

        self.stats.error_stats.is_error = False

        return self.stats
