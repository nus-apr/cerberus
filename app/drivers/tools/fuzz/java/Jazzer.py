import os
from os.path import join

from app.drivers.tools.fuzz.AbstractFuzzTool import AbstractFuzzTool


class Jazzer(AbstractFuzzTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "crhf2docker/jazzer:alpha"

    def analyse_output(self, dir_info, bug_id, fail_list):
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:
        """

        return self.stats

    def run_fuzz(self, bug_info, fuzzer_config_info):
        super().run_fuzz(bug_info, fuzzer_config_info)
        self.emit_normal("executing fuzz command")

        timeout = int(float(fuzzer_config_info[self.key_timeout]) * 60)

        self.timestamp_log_start()

        # Compile the harness first

        harness_class_dir = join(self.dir_setup, self.name, "target", "classes")
        self.ensure_command(f"mkdir -p {harness_class_dir}")

        target_class = self.read_json(join(self.dir_setup, self.name, "harness.json"))[
            "class"
        ]

        harness_source_dir = join(self.dir_setup, self.name, "src", "main", "java")

        target_src = join(harness_source_dir, self.class_name_to_file(target_class))

        classpaths = [
            join(self.dir_expr, "src", dep) for dep in bug_info["dependencies"]
        ]
        classpaths.append(join(self.dir_expr, "src", bug_info["class_directory"]))
        classpaths.extend(self.list_dir("/opt/jazzer/lib"))

        compile_command = (
            f"javac -cp '{':'.join(classpaths)}:{harness_source_dir}'"
            f" -d {harness_class_dir} {target_src}"
        )
        self.ensure_command(compile_command)

        reproducer_path = join(self.dir_output, "reproducers")
        self.ensure_command(f"mkdir {reproducer_path}")

        artifact_prefix = join(self.dir_output, "jazzer_artifacts")
        self.ensure_command(f"mkdir {artifact_prefix}")

        fuzz_command = (
            f"/opt/jazzer/jazzer --cp={':'.join(classpaths)}:{harness_class_dir} --target_class={target_class}"
            f" --reproducer_path={reproducer_path}"
            f" -artifact_prefix={artifact_prefix}"
            f" -timeout={timeout}"
        )

        # This may exit with non-zero status, which is expected
        self.run_command(fuzz_command, self.log_output_path, join(self.dir_expr, "src"))

        reproducers = self.list_dir(reproducer_path, "*.java")
        if len(reproducers) != 1:
            self.error_exit(f"Expected 1 reproducer, got {len(reproducers)}")

        reproducer_file = reproducers[0]
        s = "".join(self.read_file(reproducer_file))
        lines = self.reproducer_to_junit4(s).splitlines(keepends=True)
        self.write_file(lines, reproducer_file)

        self.timestamp_log_end()

    def ensure_command(
        self, command, log_file_path="/dev/null", dir_path=None, env=dict()
    ):
        if self.run_command(command, log_file_path, dir_path, env):
            self.error_exit(f"'{command}' fails")

    @staticmethod
    def class_name_to_file(classname):
        tmp = classname.split(".")
        tmp[-1] += ".java"
        return join(*tmp)

    @classmethod
    def reproducer_to_junit4(cls, s: str):
        lines = s.splitlines(keepends=True)

        lines.insert(0, "import org.junit.Test;\n")

        for idx, line in enumerate(lines):
            if "public static void main(String[] args) throws Throwable" in line:
                break
        else:
            raise RuntimeError("declaration of main not found")
        lines.insert(idx, "    @Test")
        lines[
            idx + 1
        ] = "    public /*static*/ void main(/*String[] args*/) throws Throwable {\n"

        for idx, line in enumerate(lines):
            if "fuzzerInitialize.invoke(null, (Object) args);" in line:
                break
        else:
            raise RuntimeError("fuzzer initialization not found")
        lines[
            idx
        ] = "                fuzzerInitialize.invoke(null, (Object) /*args*/ null);"

        return "\n".join(lines)
