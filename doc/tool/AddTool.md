# Add New Repair Tool

In order to add a new repair tool to the framework, the following requirements should be met

* Repair Driver: python class than extends AbstractTool to facilitate standardization of interfaces
* Repair Tool image (optional): to enable container virtualization, a Dockerfile is required or the tool should be invokable from the CLI
* Instrumentation (optional): for each bug in a benchmark an instrumentation script can be placed in a folder with the name of the tool and the script should be named `instrument.sh`

## Adding a Driver
Create a new file in `app/tools` with the Tool name (i.e. NewTool.py) that contains the following code:

```py

import os
import re
import shutil

from app.drivers.tools import AbstractTool
from app.core.utilities import error_exit
from app import definitions, values, emitter, container


class NewTool(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(NewTool, self).__init__(self.name)
        self.image_name = "mechtaev/angelix:1.1"

    def repair(self, bug_info, config_info):
        super(NewTool, self).repair(bug_info, config_info)
        ''' 
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output 
        '''
        # execute repair tool
        self.timestamp_log_start()
        repair_command = ""
        status = self.run_command(repair_command,
                                  log_file_path=self.log_output_path)
        self.timestamp_log_end()

    def save_artefacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        super().save_artefacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        """
            analyse tool output and collect information
            output of the tool is logged at self.log_output_path
            information required to be extracted are:

                self._space.non_compilable
                self._space.plausible
                self._space.size
                self._space.enumerations
                self._space.generated

                self._time.total_validation
                self._time.total_build
                self._time.timestamp_compilation
                self._time.timestamp_validation
                self._time.timestamp_plausible
        """
        emitter.normal("\t\t\t analysing output of " + self.name)
        return self._space, self._time, self._error


```


## Instrumenting an experiment for a tool ##
Certain tools require instrumentation in order to work properly on a given vulnerability. This instrumentation script (`instrument.sh`) has to be placed in a folder with a lowercase name of the tool in the root directory of the experiment and additional files have to be generated or constructed mantually and placed in the same folder.