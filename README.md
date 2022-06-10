# Cerberus
Cerberus is a program repair platform that provides the interface to multiple
state-of-the art program repair tools such as Prophet, Darjeeling, Angelix, F1X etc.
Encapsulating the difficulties to setup the infrastructure for repair technology, this platform provides
the necessary framework to configure a program for repair. We have integrated two popular repair
benchmarks: ManyBugs and VulnLoc. This platform also provides the necessary means for researchers to
run experiments more efficiently and effectively.


# Directory Structure
Following is the high-level directory structure for this repository which we should adhere to. The structure
is designed to allow future extensions/modifications to this repository.

```
root directory
│   README.md
│
└───infra
│   └───Dockerfile.toolName_1
│   └───Dockerfile.toolName_2
│
└───benchmark-1
│   │   meta-data.json
│   └───subject-1
│   │   │   setup.sh
│   │   └───tool-1
│   │   └───tool-2
│   │   └───tool-3
│   └───subject-2
│       │   setup.sh
│       └───tool-1
│       └───tool-2
│       └───tool-3
└───benchmark-2
│   └───subject-1
│       │   setup.sh
│       └───tool-1
│       └───tool-2
│       └───tool-3
```

There are two main files that will allow the user to run any experiment using any tool. The frontend 'Cerberus.py' file, acts as the front-end driver for the experiments
and 'meta-data' file will include information about the desired experiment, identified using a specified ID.

Additionally, for each tool a Dockerfile should be created to facilitate the creation of a docker container
which can run the intended tool with its dependencies installed. For example Dockerfile.prophet would contain
all dependencies and prophet installed such that, the driver can instantiate a docker container to run the experiment.


## Using Cerberus
Following is a simple snippet for the command to run an experiment from a selected benchmark.

```bash
source activate
cerberus --bug-index=ID --tool=[cpr/angelix/prophet/genprog/fix2fit/vulnfix] --benchmark=[manybugs/vulnloc]
```
