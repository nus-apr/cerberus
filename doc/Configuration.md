# Configuration files

## Intrduction

Cerberus started as a command line interface tool but with the creation of the Program Repair Competition, we have developed a more advanced configuration module, which would allow for easier orchestration of running various subjects on different tools in different profiles. An example config file `config.json` is provided in the root directory of the repository to allow for a template `cerberus -c config/config.json`.

## Structure

The config file is based on 4 big chunks - `general`, `tasks`, `profiles`.

* The `general` object contains the configuration options which are specific for the current invocation of Cerberus.
* The `tasks` contains two objects - `default` which is a template for a task (this will be expanded upon later) and the `chunks` array, which contains a list of chunks.
* The `profiles` object contains two lists - one for the task profiles and another for the container profiles.
## The Chunks

A chunk is considered a task type, a list of benchmarks with the specified bug indices or bug subjects and a list of tools with associated extra parameters. For example, in the file `config/config_example.json`, there are 3 chunks, all of which are for the repair task - the first chunk takes the 28th and 29th bugs of the `vulnloc` benchmark and runs the `extractfix` and `vulnfix` tools. The second chunk only executes `extractfix` on the 31st, 32nd and 33rd bugs. The last chunk runs the `refactory` tool on the first three bugs of the `refactory` benchmark.

As most runs will be the same, the `default` object is used as the set of configuration parameters, but chunks can override these fields if required.  For example, one can add more repair profiles to run the `extractfix` tool.