# Cerberus Framework
Cerberus is a program repair framework that provides the interface to multiple
state-of-the art program repair tools such as Prophet, Darjeeling, Angelix, F1X etc.
Encapsulating the difficulties to setup the infrastructure for repair technology, this platform provides
the necessary framework to configure a program for repair. We have integrated two popular repair
benchmarks: ManyBugs and VulnLoc. This platform also provides the necessary means for researchers to
run experiments more efficiently and effectively.


## Features

* Execution of repair tools on benchmarks of bugs
* Configuration of the environment to execute repair tools properly on the bugs
* Concurrent execution of multiple repair tools 
* Compilation-Free validation

## Using Cerberus
Following is a simple snippet for the command to run an experiment from a selected benchmark.

```bash
source activate
cerberus --bug-index=ID  --benchmark=[manybugs/vulnloc] --tool=[cpr/angelix/prophet/f1x]
```


## Supported Repair Tools
  
| #  | Tool          | Language | Repository                          | Commit id |  
| -- | ------------- | -------- | ----------------------------------- | --------- |  
| 1  | Angelix       | C/C++    | https://github.com/mechtaev/angelix | 01396ac |  
| 2  | Prophet       | C/C++    | https://github.com/rshariffdeen/prophet | 5f8c688 |  
| 3  | Darjeeling    | C/C++    | https://github.com/squareslab/darjeeling | ed6fb3e |  
| 4  | CPR           | C/C++    | https://github.com/rshariffdeen/CPR  | 4863c60 |  
| 5  | VulnFix       | C/C++    | https://github.com/yuntongzhang/vulnfix | 44bdbab |  
| 6  | F1X           | C/C++    | https://github.com/mechtaev/f1x | e4a225e |  
| 7  | Fix2Fit       | C/C++    | https://github.com/gaoxiang9430/Fix2Fit  | 349e4ba |  
| 8  | SenX          | C/C++    | N/A      | N/A |  
| 9  | GenProg       | C/C++    | https://github.com/squaresLab/genprog-code      | 0b25153  |  
| 10 | CrashRepair   | C/C++    | https://github.com/rshariffdeen/CrashRepair     | 23430d9 |


## Supported Benchmarks of Bugs

| # | Benchmark      | Language | # Projects | # Bugs |  
| - | -------------- | -------- | ----------:| ------:|  
| 1 | ManyBugs       | C/C++    |          6 |     60 |  
| 2 | VulnLoc        | C/C++    |         11 |     43 |  


## Bugs ##
Cerberus should be considered alpha-quality software. Bugs can be reported here:

    https://github.com/rshariffdeen/cerberus/issues

## Documentation ##

* [Getting Started](doc/GetStart.md)
* [Example Usage](doc/Examples.md)
* [Manual](doc/Manual.md)
* [Extending](doc/Extending.md)


# Contributions 
We welcome contributions to improve this work, see [details](doc/Contributing.md)

## Developers ##
* Ridwan Shariffdeen
* Gao Xiang
* Yannic Noller
* Zhang Yuntong


# License
This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details

