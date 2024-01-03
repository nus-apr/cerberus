# Adding a new task profile

Currently Cerberus reads the task profiles in the file `profiles/task-default.json`. When custom configuration files are used, the profiles are defined there. Check [how to use the custom configuration files](/doc/Configuration.md) for such cases.

A profile is a json object with a field `id` and can contain any other fields which are used by the specific tasks. Commonly used fields are `timeout` and `fault_location`.

Currently used fields:

* `id`
* `timeout` - floating point value, denoting the hours, allowed for the execution of the task
* `fault_location` - fault localization information provision with currently values:
  * `auto` - the tool has the responsibility of gathering such information
  * `dev`  - if the benchmark provides this information, it will be accessible
  * `file` - if the benchmark provides this information, it will be accessble but only on file level granularity
  * `line` - if the benchmark provides this information, it will be accessble but only on line level granularity
* `passing_test_ratio`
