# Project Architecture

## Benchmark

The benchmark folder contains all possible benchmarks which can be dynamically instantiated when Cerberus is started. A benchmark is stored locally or can be set as a github submodule. (Check [how to add a benchmark](benchmark/AddBenchmark.md)) for more information.

## App
This is the root directory of the project. It contains all code for the project.

### Core

 * The abstractions file contains abstractions over operations, which are dependent on whether Cerberus is using containers for the experiments or running them locally.
 * The args file contains the command line argument definitions.
 * The configuration file contains the dynamic loading and command line argument parsing.
 * The container file contains all the methods used for interaction with the containers created. Cerberus uses the official [Docker Python SDK](docker-py.readthedocs.io/).
 * The definitions file contains all constants used across the project, allowing for a unified "magic string" storage.
 * The emitter file contains helper methods to help with outputting the data in a terminal friendly manner.
 * The logger file contains helper methods to help with outputting the data in a logger friendly manner.
 * The main file is the main entry file, which gets started.
 * The parallel file contains logic for parallel evaluation of files. **NOT YET IMPLEMENTED**
 * The reader file contains helper methods for deserializing files.
 * The utilities file contains helper methods.
 * The values file contains global variables and runtime state.
 * The writer file contains helper methods for serializing files.

#### Task

The task module contains all operations which Cerberus supports. Currently they are analyze and repair with fuzzing in development. Inside this module the analysis functionality is store, statistics and the TaskStatus enumerable.

#### Configs

The configs module contains the new configuration processing logic. More information in [the specialized documentation file](AdvancedConfiguration.md).

### Drivers

The drivers folder contains two folders - benchmarks and tools.

* The tools folder contains all possible tools. (Check [how to add a tool](benchmark/AddTool.md)) for more information.
* The benchmarks folder contains all possible benchmarks. (Check [how to add a bencjmark](benchmark/AddBenchmark.md)) for more information.

### Notification

The notification module currently supports sending messages via Slack, Discord or email to notify of the completion of Cerberus.
This module will be more tightly integrated later on.

### Plugins

* Valkyrie - Not Yet Implemented. Future work

### UI

The main module providing everything needed to have a user interface in the terminal. By default image creation of experiment subjects is parallelized and simiarly for the experiments themselves.

