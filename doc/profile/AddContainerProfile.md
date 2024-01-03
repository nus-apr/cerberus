# Adding a new container profile

Currently Cerberus reads the containr profiles in the file `profiles/container-default.json`. A container profile is a json object with a field `id`, which is used by the container and UI module to handle resource allocation. A container profile currently supports the following set of fields:

* `cpu_count` - amount of cpus allowed for a task
* `gpu_count` - amount of gpus allowed for a task
* `mem_limit` - maximum amount of RAM the task can use before being terminated
* `enable_network` - allow the tool to have a network connection to the outside world, i.e. calling an external service