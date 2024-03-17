# Add New Bug Benchmark

In order to add a new benchmark to the framework, the following requirements should be met:

* Benchmark Driver: a Python class than extends AbstractBenchmark to facilitate standardization of interfaces
* Benchmark Image: a Dockerfile describing how to construct the benchmark container
* Benchmark metadata file: A Json file containing an array of objects with the following features

## Adding a Driver

Create a new file in `app/drivers/benchmarks/<language of benchmark>` with the Benchmark name (i.e. `NewBenchmark.py`) that contains the following code:

```py
import shutil
import os
from os.path import join
from typing import Dict
from typing import Optional
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.core.utilities import execute_command
from app import definitions, values, emitter


class NewBenchmark(AbstractBenchmark):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(NewBenchmark, self).__init__()

    def setup_experiment(
        self, bug_index: int, container_id: Optional[str], test_all: bool
    ) -> bool:
        is_error = super(Defects4J, self).setup_experiment(
            bug_index, container_id, test_all
        )
        experiment_item = self.experiment_subjects[int(bug_index) - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        is_error = status != 0
        if not is_error:
            if self.verify(bug_id, container_id):
                emitter.success("\t\t\t[benchmark] verified successfully")
            else:
                emitter.error("\t\t\t[benchmark] verification failed")
                is_error = True
        return is_error

    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
        emitter.normal("\t\t\tdownloading experiment subject")
        return True

    def config(self, bug_index: int, container_id: Optional[str]) -> bool:
        emitter.normal("\t\t\tconfiguring experiment subject")
        return True

    def build(self, bug_index: int, container_id: Optional[str]) -> bool:
        emitter.normal("\t\t\tbuilding experiment subject")
        return True

    def test(self, bug_index: int, container_id: Optional[str]) -> bool:
        emitter.normal("\t\t\ttesting experiment subject")
        return True

    def verify(self, bug_index: int, container_id: Optional[str]) -> bool:
        emitter.normal("\t\t\tverify dev patch and test-oracle")
        return True

    def transform(self, bug_index: int, container_id: Optional[str]) -> bool:
        emitter.normal("\t\t\ttransform fix-file")
        return True

    def clean(self, exp_dir_path: str, container_id: Optional[str]) -> None:
        emitter.normal("\t\t\tremoving experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artefacts(self, dir_info, container_id):
        emitter.normal("\t\t[benchmark] saving experiment artefacts")
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(Defects4J, self).save_artefacts(dir_info, container_id)
```

## Benchmark folder

Create a new folder in `benchmarks` with the benchmark name in lowercase (i.e. `newbenchmark`). The folder should contain the following files:

* Dockerfile, describing how the benchmark image is constructed
* meta-data.json containing information about every experiment
* Optional - folders for every subject and subfolders for every bug
* Optional - base folder which contains files common to all projects (test cases, images, etc.).

Below is an example tree structure of a benchmark with accompanying example Dockerfile and meta-data.json structure.

### File structure

```bash
newbenchmark
├── base
├── Dockerfile
├── meta-data.json
├── subject-a
│   ├── 1
│   └── 2
└── subject-b
    └── 1
```

Below we provide an example Dockerfile for a Python oriented benchmark.

## Example Dockerfile

```dockerfile
FROM ubuntu:20.04
LABEL maintainer="Dev <dev@nus-apr.com>"

RUN apt-get update && apt-get upgrade -y && apt-get autoremove -y
RUN apt-get install python3 python3-pip -y
RUN pip3 install pytest pytest-timeout
```

## Example metadata

The metadata file has a couple of mandatory fields, which Cerberus directly utilises to automatically find files or execute certain operations. Below an example file is provided for multiple bigs and an example file structure. We allow any fields in the `meta-data.json` file, which can be utilised by the driver and subsequently the tool with some already standardized for the different languages:

* Mandatory:
  * `id` - numeric identifier, used by Cerberus, the command line arguments --bug-index and --bug-index-list check for it
  * `subject` - name of the specific program which will be repaired
  * `bug_id` - sub-identifier allowing for identifying different bugs for the same subject
  * `line_numbers` - perfect fault localization information, can be empty
  * `bug_type` - a textual description of the type of bug, e.g. `Test Failure`, `Null Pointer Dereferencing` - used by some repair tools as a parameter for repair patterns or instrumentation
  * `test_timeout` - default time (in minutes) needed for the execution of a test
  information
* Common but not mandatory:
  * `source_file` - The specific file containing the bug
  * `failing_test_identifiers` - A string or a list containing test identifiers for tests which fail
  * `passing_test_identifiers` -  A string or a list containing test identifiers for tests which pass
  * `count_pos` - The amount of tests in `failing_test_identifiers`
  * `count_neg` - The amount of tests in `passing_test_identifiers`
  * `config_script` - A path to the name of the configuration script. The path is relative to the directory of the bug, e.g. `subject-a/1`
  * `build_script` - A path to the configuration script for the bug. The path is relative to the directory of the bug, e.g. `subject-a/1`
  * `clean_script`  - A path to the clean-up script for the bug. The path is relative to the directory of the bug, e.g. `subject-a/1`
  * `build_script`  - A path to the build script for the bug. The path is relative to the directory of the bug, e.g. `subject-a/1`
  * `test_script` - A path to the test script for the bug. The path is relative to the directory of the bug, e.g. `subject-a/1`. The script should be able to accept the keyword `all` to allow for execution of all tests or the identifier for test. This can be benchmark specific but a preferable standard can be either a file path to indicate input files or name of a test method `file::method`.
  * `language` - The language of the subject. `multi` if there is more than one
  * `binary_args` - command to execute the binary. `$POC` represents where the input should be passed
  * `exploit_file_list` - a list of crashing inputs. Similar to `failing_test_identifiers`
* Java:
  * `dependencies` - specific dependencies of the project.
  * `source_directory` - the location of the .java files for the project. Path is relative to the root of the project.
  * `class_directory` - the location of generated .class files for the project. Path is relative to the root of the project.
  * `test_directory`  - the location of .java files for the tests. Path is relative to the root of the project.
  * `test_class_directory` - the location of generated .class files for the tests. Path is relative to the root of the project.
  * `java_version` - The specific Java version used by the bug, e.g. 8, 11, 14
  * `build_system` - The specific build system for the bug, e.g. Maven, Gradle, Ant
* Python:
  * `test_framework` - The name of the test framework being used.
* C/C++:
  * `binary_path` - location of the binary to be executed. The path is relative to the root folder of the bug


```json
[{
        "id": 1,
        "subject": "subject-a",
        "bug_id": "1",
        "line_numbers": [],
        "language": "",
        "bug_type": "Test Failure",
        "failing_test_identifiers": [
            "Test Identifier",
        ],
        "passing_test_identifiers": [
            "Test Identifier"
        ],
        "count_neg": 1,
        "count_pos": 1,
        "config_script": "config_subject",
        "build_script": "build_subject",
        "clean_script": "clean_subject",
        "test_script": "test_subject",
        "test_timeout": 5,
    },
    {
        "id": 2,
        "subject": "subject-a",
        "bug_id": "2",
        "line_numbers": [],
        "language": "",
        "bug_type": "Test Failure",
        "failing_test_identifiers": [
            "Test Identifier",
        ],
        "passing_test_identifiers": [
            "Test Identifier"
        ],
        "count_neg": 1,
        "count_pos": 1,
        "config_script": "config_subject",
        "build_script": "build_subject",
        "clean_script": "clean_subject",
        "test_script": "test_subject",
        "test_timeout": 5,
    },
    {
        "id": 3,
        "subject": "subject-b",
        "bug_id": "1",
        "line_numbers": [],
        "language": "",
        "bug_type": "Test Failure",
        "failing_test_identifiers": [
            "Test Identifier",
        ],
        "passing_test_identifiers": [
            "Test Identifier"
        ],
        "count_neg": 1,
        "count_pos": 1,
        "config_script": "config_subject",
        "build_script": "build_subject",
        "clean_script": "clean_subject",
        "test_script": "test_subject",
        "test_timeout": 5,
    }
]
```

## Tool Instrumentation


To allow for tool specific instrumentation, one can construct a folder inside of the bug folder with the name of the tool as the folder name. For example, we would like to add instrumentation for bug 1 in subject-a for the CPR tool. To do this, one can create the folder `newbenchmark/subject-a/1/cpr` with a file named `instrument.sh` to execute any extra steps before the tool is executed on the buggy program.
