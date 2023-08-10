import multiprocessing as mp
import os
import re
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Darjeeling(AbstractRepairTool):

    CONFIG_C_TEMPLATE = """
algorithm:
  type: exhaustive
coverage:
  method:
    type: gcov
localization:
  type: spectrum-based
  metric: tarantula
{fix_file_list}
optimizations:
  ignore-dead-code: true
  ignore-equivalent-insertions: true
  ignore-string-equivalent-snippets: true
program:
  build-instructions:
    steps:
    - command: ./{config_script}
      directory: {dir_setup}
    - command: ./{build_script}
      directory: {dir_setup}
    steps-for-coverage:
    - command: CFLAGS="--coverage " CXXFLAGS="--coverage "  LDFLAGS="--coverage " ./{config_script}
      directory: {dir_setup}
    - command: CFLAGS="--coverage " CXXFLAGS="--coverage " LDFLAGS="--coverage " ./{build_script}
      directory: {dir_setup}
    time-limit: 30
  image: {tag_id}-runtime
  language: {prog_language}
  source-directory: {dir_src}
  tests:
    tests:
{test_cases}
    time-limit: 5
    type: shell
    workdir: {dir_setup}
resource-limits:
  candidates: 100000
seed: 0
threads: 1
transformations:
  schemas:
  - type: delete-statement
  - type: append-statement
  - type: prepend-statement
  - type: replace-statement
version: 1.0
    """
    CONFIG_PYTHON_TEMPLATE = """
version: '1.0'
seed: 0
threads: 1
localization:
  type: spectrum
  metric: tarantula
algorithm:
  type: exhaustive
coverage:
  method:
    type: coverage.py
{fix_file_list}
program:
  image: {tag_id}-runtime
  language: python
  source-directory: {dir_src}
  build-instructions:
    time-limit: 1
    steps: []
    steps-for-coverage: []
  tests:
    type: pytest
    workdir: {dir_src}
    tests:
{test_cases}
transformations:
  schemas:
    - type: delete-statement
    - type: replace-statement
    - type: prepend-statement
    - type: append-statement
optimizations:
  use-scope-checking: false
  use-syntax-scope-checking: false
  ignore-dead-code: false
  ignore-equivalent-insertions: false
  ignore-untyped-returns: false
  ignore-string-equivalent-snippets: false
  ignore-decls: false
  only-insert-executed-code: false
resource-limits:
  candidates: 10000
    """

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/darjeeling"

    def generate_repair_config(
        self,
        c_script,
        b_script,
        t_script,
        p_lang,
        fix_files,
        tag_id,
        test_driver,
        test_list,
    ):
        self.emit_normal(f"generating config file for {self.name}")
        config_file_path = join(self.dir_setup, "darjeeling.yml")
        file_list_str = ""
        if fix_files:
            file_list_str = "  restrict-to-files:\n"
            for f in fix_files:
                file_list_str += f"  - {f}\n"

        config_content = ""
        if p_lang.lower() in ["c", "c++"]:
            test_cases_str = ""
            for t in test_list:
                test_cases_str += f"    - ./{test_driver} {t}\n"
            config_content = self.CONFIG_C_TEMPLATE.format(
                config_script=c_script,
                build_script=b_script,
                test_script=t_script,
                prog_language=p_lang,
                fix_file_list=file_list_str,
                tag_id=tag_id,
                dir_src=join(self.dir_expr, "src"),
                dir_setup=self.dir_setup,
                test_cases=test_cases_str,
            )
        elif p_lang.lower() == "python":
            test_cases_str = ""
            for t in test_list:
                test_cases_str += f"    - {t}\n"
            config_content = self.CONFIG_PYTHON_TEMPLATE.format(
                test_script=t_script,
                prog_language=p_lang,
                fix_file_list=file_list_str,
                tag_id=tag_id,
                dir_src=join(self.dir_expr, "src"),
                test_cases=test_cases_str,
            )
        else:
            self.error_exit(f"unsupported programming language {p_lang}")
        self.write_file(config_content, config_file_path)
        return config_file_path

    def generate_runtime_dockerfile(self, docker_image_tag):
        # the dockerfile is created at the setup dir and docker build will be run at the setup dir
        self.emit_normal(f"generating runtime Dockerfile for {self.name}")
        dockerfile_path = self.dir_setup + "/Dockerfile"
        self.write_file(
            [
                f"FROM {docker_image_tag}\n",
                "USER root\n",
                "RUN apt update; apt install -y make g++\n",
                "RUN pip3 install coverage pytest pytest-cov\n",
                f"RUN cd {self.dir_setup}; make clean;make distclean;rm CMakeCache.txt; exit 0\n",
                "WORKDIR /experiment\n",
            ],
            dockerfile_path,
        )
        return dockerfile_path

    def build_runtime_docker_image(self, docker_tag):
        dockerfile_path = self.generate_runtime_dockerfile(docker_tag)
        self.emit_normal(f"building runtime Dockerfile for {self.name}")
        build_command = (
            f"sudo docker build -t {docker_tag}-runtime -f {dockerfile_path} ."
        )
        log_docker_build_path = join(self.dir_logs, "darjeeling-docker.log")
        self.run_command(
            build_command, dir_path=self.dir_setup, log_file_path=log_docker_build_path
        )

    def run_repair(self, bug_info, repair_config_info):
        config_script = bug_info.get(self.key_config_script, None)
        build_script = bug_info.get(self.key_build_script, None)
        test_script = bug_info.get(self.key_test_script, None)
        prog_lang = bug_info.get(self.key_language, None)

        if not prog_lang:
            self.error_exit(
                f"{self.name} requires bug to specify the programming language"
            )
        if not config_script and prog_lang not in ["python"]:
            self.error_exit(f"{self.name} requires a configuration script as input")
        if not build_script and prog_lang not in ["python"]:
            self.error_exit(f"{self.name} requires a build script as input")
        if not test_script:
            self.error_exit(f"{self.name} requires a test script as input")

        benchmark_name = bug_info.get(self.key_benchmark)
        subject_name = bug_info.get(self.key_subject)
        bug_id = str(bug_info[self.key_bug_id])
        docker_tag_id = f"{self.name}-{benchmark_name}-{subject_name}-{bug_id.lower()}"
        test_list = bug_info.get(self.key_passing_tests) + bug_info.get(
            self.key_failing_tests
        )
        self.build_runtime_docker_image(docker_tag_id)
        self.generate_repair_config(
            c_script=config_script,
            b_script=build_script,
            t_script=test_script,
            p_lang=str(prog_lang).lower(),
            fix_files=[bug_info[self.key_fix_file]],
            tag_id=docker_tag_id,
            test_driver=test_script,
            test_list=test_list,
        )
        super(Darjeeling, self).run_repair(bug_info, repair_config_info)
        if self.is_instrument_only:
            return

        timeout = str(repair_config_info[self.key_timeout])
        additional_tool_param = repair_config_info[self.key_tool_params]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(
                str(self.current_task_profile_id.get("NA")), self.name.lower(), bug_id
            ),
        )
        dir_patch = self.dir_output + "/patches"

        mkdir_command = "sudo mkdir -p {}".format(dir_patch)
        self.run_command(mkdir_command, self.log_output_path, self.dir_expr)

        repair_command = "timeout -k 5m {}h  ".format(str(timeout))
        if self.container_id:
            repair_command += "sudo "
        repair_command += "darjeeling repair --continue --patch-dir {} ".format(
            dir_patch
        )
        repair_command += additional_tool_param + " "
        if self.is_dump_patches:
            repair_command += " --dump-all "
        repair_command += " darjeeling.yml"
        self.timestamp_log_start()
        status = self.run_command(
            repair_command, self.log_output_path, dir_path=self.dir_setup
        )
        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("[warning] no log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        time_stamp_first_plausible = None
        time_stamp_first_validation = None
        time_stamp_first_compilation = None

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].rstrip()
            self.stats.time_stats.timestamp_end = log_lines[-1].rstrip()
            for line in log_lines:
                if "evaluated candidate" in line:
                    self.stats.patch_stats.enumerations += 1
                    if time_stamp_first_validation is None:
                        time_stamp_first_validation = line.split(" | ")[0]
                elif "found plausible patch" in line:
                    self.stats.patch_stats.plausible += 1
                    if time_stamp_first_plausible is None:
                        time_stamp_first_plausible = line.split(" | ")[0]
                elif "validation time: " in line:
                    time = (
                        line.split("validation time: ")[-1]
                        .strip()
                        .split("\x1b")[0]
                        .split(".0")[0]
                    )
                    self.stats.time_stats.total_validation += float(time)
                elif "build time: " in line:
                    time = (
                        line.split("build time: ")[-1]
                        .strip()
                        .split("\x1b")[0]
                        .split(".0")[0]
                    )
                    self.stats.time_stats.total_build += float(time)
                    if time_stamp_first_compilation is None:
                        time_stamp_first_compilation = line.split(" | ")[0]
                elif "possible edits" in line:
                    self.stats.patch_stats.size = int(line.split(": ")[2].split(" ")[0])
                elif "plausible patches" in line:
                    self.stats.patch_stats.plausible = int(
                        line.split("found ")[-1]
                        .replace(" plausible patches", "")
                        .split("\x1b")[0]
                        .split(".0")[0]
                    )

        self.stats.patch_stats.generated = len(
            self.list_dir(
                join(
                    self.dir_output,
                    "patch-valid" if self.use_valkyrie else "patches",
                )
            )
        )

        return self.stats
