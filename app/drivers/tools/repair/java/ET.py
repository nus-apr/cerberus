import os
import json
from pathlib import Path

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class ET(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        #self.image_name = "et-dev"
        self.image_name = "xmcp/et:231004.2"
        self.hash_digest = "sha256:78351cfb9bafad82d61bc594719f22f4f596ad52da669bc98bd856ef640e7c27"

    def run_repair(self, bug_info, repair_config_info):
        super(ET, self).run_repair(bug_info, repair_config_info)
        self.timestamp_log_start()

        print('!!! begin')
        #return #####

        assert bug_info['language']=='java'
        assert len(bug_info['failing_test'])>0

        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        repo_path = (Path(self.dir_expr) / 'src').resolve()
        setup_path = Path(self.dir_setup).resolve()
        #print(bug_info, repair_config_info, self.container_id)

        # test list maybe `com.clz::mtd` or `com.clz`, let's make them into `com.clz`

        test_failed = []
        test_failed_set = set()
        for t in bug_info['failing_test']:
            t = t.partition('::')[0]
            if t not in test_failed_set:
                test_failed_set.add(t)
                test_failed.append(t)

        test_passed = []
        test_passed_set = set()
        for t in bug_info['passing_test']:
            t = t.partition('::')[0]
            if t not in test_failed_set and t not in test_passed_set:
                test_passed_set.add(t)
                test_passed.append(t)

        self.write_json({
            'id': int(bug_info['id']),
            'repo_path': str(repo_path),
            'setup_script_path': str(setup_path),

            'sp_src': bug_info['source_directory'],
            'sp_test': bug_info['test_directory'],
            'tp_src': bug_info['class_directory'],
            'tp_test': bug_info['test_class_directory'],
            'cp_compile': ':'.join([str(Path(self.dir_expr)/s) for s in bug_info['dependencies']]),
            'cp_test': ':'.join([
                str(repo_path/bug_info['class_directory']),
                str(repo_path/bug_info['test_class_directory']),
                *[str(Path(self.dir_expr)/s) for s in bug_info['dependencies']],
            ]),
            'lang_level': bug_info['java_version'],

            'test_passed': test_passed,
            'test_failed': test_failed,
            'test_timeout': bug_info['test_timeout'],
            'test_sh_fn': bug_info['test_script'],

            'total_timeout_s': int(float(repair_config_info['timeout'])*3600),
            'cpu_count': len(repair_config_info['cpus']),
            'gpu_count': len(repair_config_info['gpus']),
        }, '/root/workflow/info.json')

        ret = self.run_command('bash -c "python3 /root/workflow/main.py"', log_file_path='/root/workflow/log.txt')

        #print(*self.read_file('/root/workflow/log.txt'), sep='')

        self.process_status(ret)
        self.timestamp_log_end()

        print('!!! end')

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """

        # tbar_patches_dir = join(self.tbar_root_dir, "OUTPUT")
        # self.run_command("cp -r {0} {1}".format(tbar_patches_dir, self.dir_output))

        self.run_command(f'cp -r /root/workflow/log.txt {self.dir_output}/')
        self.run_command(f'cp -r /root/workflow/fl {self.dir_output}/')
        self.run_command(f'cp -r /root/workflow/repair {self.dir_output}/')
        self.run_command(f'cp -r /root/workflow/patches {self.dir_output}/')
        super().save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
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
            stats = self.read_json('/root/workflow/repair/stats.json')
        except Exception as e:
            print('cannot read stats', repr(e))
            stats = None

        if not stats:
            self.stats.error_stats.is_error = True
            return

        self.stats.patch_stats.size = stats['n_generated']
        self.stats.patch_stats.enumerations = stats['n_validated']
        self.stats.patch_stats.non_compilable = stats['n_validated'] - stats['n_compilable']
        self.stats.patch_stats.plausible = stats['n_plausible']
        self.stats.patch_stats.generated = stats['n_plausible']

        self.stats.error_stats.is_error = False

        return self.stats
