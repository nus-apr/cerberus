# Project Architecture

## App

### Benchmarks
The benchmarks folder contains all possible benchmarks which will be dynamically instantiated when Cerberus is started. (Check [how to add a benchmark](benchmark/AddBenchmark.md)) for more information.

### Tools
The tools folder contains all possible tools which will be dynamically instantiated when Cerberus is started. (Check [how to add a tool](benchmark/AddTool.md)) for more information.

### Abstractions
The abstractions file contains abstractions over operations, which are dependent on whether Cerberus is using containers for the experiments or running them locally. 

### Analysis
The analysis file contains the classes storing (space,time) analysis information.

### Configuration
The configuration file contains the dynamic loading and command line argument parsing.

### Container
The container file contains all the methods used for interaction with the container. Cerberus uses the python version of the sdk. 

### Definitions
The definitions file contains all constants used across the project, allowing for a unified "magic" string storage. 

### Emitter
The emitter file contains helper methods to help with outputting the data in a terminal friendly manner.

### Logger
The logger file contains helper methods to help with outputting the data in a logger friendly manner.

### Main
This is the main entry file, which gets started.

### Parallel
#### Not Yet Implemented. Future work.
The parallel file contains logic for parallel evaluation of files.

### Reader
The reader file contains helper methods for deserializing files.

### Repair
The repair file contains the main orchestration logic, which Cerberus uses.

### Utilities
The utilities file contains helper methods, which have various utilities

### Valkyrie
#### Not Yet Implemented. Future work. 

### Values
The values file contains all the variables, which change depending on the configuration flags

### Writer
The writer file contains helper methods for serializing files.

