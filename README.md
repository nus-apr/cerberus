# APR-Study
Evaluation of different APR techniques on ManyBugs benchmark

# Directory Structure
Following is the high-level directory structure for this repository which we should adhere to. The structure
is designed to allow future extensions/modifications to this repository. 

```
root directory
│   README.md│    
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
    │   meta-data.json
    │   file021.txt
    │   file022.txt
```

There are two main files that will allow the user to run any experiment using any tool. The 'driver.py' file, as the name
indicates acts as the front-end driver for the experiments and 'meta-data' file will include information on how to
run the desired experiment using a given ID.

Additionally, for each tool a Dockerfile should be created to facilitate the creation of a docker container
which can run the intended tool with its dependencies installed. For example Dockerfile.prophet would contain
all dependencies and prophet installed such that, the driver can instantiate a docker container to run the experiment. 


## Using Driver
The driver is a frontend to run all experiments with different tools

```bash
python3.7 driver.py --bug-id=ID --tool-name=[cpr/angelix/prophet/genprog/fix2fit]
```

## TODO

### Gao Xiang
* update Dockerfile.fix2fit to create a self-contained container for Fix2Fit and experiments
* implement the interface in driver.py for Fix2Fit (see reference for CPR)


### Jyoti
* update Dockerfile.genprog to create a self-contained container for Fix2Fit and experiments
* implement the interface in driver.py for GenProg (see reference for CPR)

### Ridwan
* update Dockerfiles to create a self-contained container for Angelix/Prophet and experiments
* implement the interface in driver.py for Angelix/Prophet (see reference for CPR)
