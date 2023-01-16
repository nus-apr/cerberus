# Cerberus Framework

Cerberus is a program repair framework that provides the interface to multiple
state-of-the art program repair tools such as Prophet, Darjeeling, Angelix, F1X etc.
Encapsulating the difficulties to setup the infrastructure for repair technology, this platform provides
the necessary framework to configure a program for repair. We have integrated multiple repair
benchmarks including but not limited to ManyBugs, VulnLoc and Defects4J. This platform also provides the necessary means for researchers to
run experiments more efficiently and effectively.

## Features

* Execution of repair tools on benchmarks of bugs
* Configuration of the environment to execute repair tools properly on the bugs
* Concurrent execution of multiple repair tools
* Artifacts are extracted and stored for each experiment

## Installation Procedure

To ensure that Cerberus has all dependencies one has to run `pip install -r requirements.txt` before trying to use Cerberus

## Using Cerberus

Following is a simple snippet for the command to run an experiment from a selected benchmark.

```bash
source activate
cerberus --bug-index=ID  --benchmark=[manybugs/vulnloc] --tool=[cpr/angelix/prophet/f1x]
```

## Supported Repair Tools
  
| #  | Tool          | Language | Repository                                        | Commit id |  
| -- | ------------- | -------- | ------------------------------------------------- | --------  |  
| 1  | Angelix       | C/C++    | <https://github.com/mechtaev/angelix>             | 01396ac   |  
| 2  | Prophet       | C/C++    | <https://github.com/rshariffdeen/prophet>         | 5f8c688   |  
| 3  | Darjeeling    | C/C++    | <https://github.com/squareslab/darjeeling>        | ed6fb3e   |  
| 4  | CPR           | C/C++    | <https://github.com/rshariffdeen/CPR>             | 4863c60   |  
| 5  | VulnFix       | C/C++    | <https://github.com/yuntongzhang/vulnfix>         | 44bdbab   |  
| 6  | F1X           | C/C++    | <https://github.com/mechtaev/f1x>                 | e4a225e   |  
| 7  | Fix2Fit       | C/C++    | <https://github.com/gaoxiang9430/Fix2Fit>         | 349e4ba   |  
| 8  | SenX          | C/C++    | N/A                                               | N/A       |  
| 9  | GenProg       | C/C++    | <https://github.com/squaresLab/genprog-code>      | 0b25153   |  
| 10 | ExtractFix    | C/C++    | N/A                                               | N/A       |
| 11 | Verifix       | C/C++    | <https://github.com/zhiyufan/Verifix>             | 6d5bda0   |
| 12 | Hippodrome    | Java     | <https://github.com/verse-lab/hippodrome>         | 012f291   |
| 13 | SequenceR     | Java     | <https://github.com/KTH/sequencer>                | 3bd0cd4   |
| 14 | ARJA          | Java     | <https://github.com/yyxhdy/arja>                  | e795032   |
| 15 | Cardumen      | Java     | <https://github.com/SpoonLabs/Astor>              | f11f0b8   |
| 16 | jMutRepair    | Java     | <https://github.com/SpoonLabs/Astor>              | f11f0b8   |
| 17 | jKali         | Java     | <https://github.com/SpoonLabs/Astor>              | f11f0b8   |
| 18 | jGenProg      | Java     | <https://github.com/SpoonLabs/Astor>              | f11f0b8   |



## Supported Benchmarks of Bugs

| # | Benchmark         | Language | Repository                                        | # Projects | # Bugs |  
| - | ----------------- | -------- | ------------------------------------------------- | ----------:| ------:|  
| 1 | ManyBugs          | C/C++    | <https://github.com/nus-apr/manybugs>             |          6 |     60 |  
| 2 | VulnLoc           | C/C++    | <https://github.com/nus-apr/vulnloc-benchmark>    |         11 |     43 |  
| 3 | ExtractFix        | C/C++    | <https://github.com/nus-apr/extractfix-benchmark> |          7 |     30 |
| 4 | ITSP              | C/C++    | <https://github.com/nus-apr/itsp-benchmark>       |         10 |    661 |
| 5 | Hippodrome        | Java     | <https://github.com/nus-apr/hippodrome-benchmark> |         16 |     25 |
| 6 | Defects4J         | Java     | <https://github.com/nus-apr/defects4j>            |          6 |     75 |

## Bugs

Cerberus should be considered alpha-quality software. Bugs can be reported here:

    https://github.com/nus-apr/cerberus/issues

## Documentation

* [Getting Started](doc/GetStart.md)
* [Example Usage](doc/Examples.md)
* [Manual](doc/Manual.md)
* [Extending](doc/Extending.md)
* [Project Architecture](doc/ProjectArchitecture.md)

# Contributions

We welcome contributions to improve this work, see [details](doc/Contributing.md)

# Developing

## Developers

* Ridwan Shariffdeen
* Martin Mirchev
* Zhang Yuntong

## Contributors

* Gao Xiang
* Yannic Noller

# License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details
