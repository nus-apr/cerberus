# Analyze Tool
The following document describes the interface of the AbstactAnalyzeTool class - the order of the methods defined represnts the order in which they are ran by Cerberus

```py

class NewTool(AbstractAnalyzeTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(NewTool, self).__init__(self.name)
        self.image_name = "mechtaev/angelix:1.1"
```
The constructor should follow the following format, the line `self.image_name=...` should be an identifier for a valid docker image, preferably with a label.

```py
     def invoke(self, bug_info, task_config_info):
        '''
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        '''
        # execute repair tool
        self.timestamp_log_start()
        analysis_command = ""
        status = self.run_command(analysis_command,
                                  log_file_path=self.log_output_path)
        self.process_status(status) # Delegate the return code of the command to a general method
        self.timestamp_log_end()
```
Start the repair tool. Preferably `self.timestamp_log()` is called before and after the `self.run_command` method to ensure easy tracing of the exact timing.

```py
    def save_artefacts(self, dir_info):
```
Save useful artifacts from the repair execution, the main folders one should transfer the results is to the output folder (`self.dir_output`) and the logs folder (`self.dir_logs`). The parent method should be invoked at the end to archive the results.

```py
    def analyse_output(self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]):
        emitter.normal("\t\t\t analysing output of " + self.name)
        return self.stats
```
Analyse the output of the tool to gather certain properties if they are defined. Output of the tool should be logged at `self.log_output_path`.