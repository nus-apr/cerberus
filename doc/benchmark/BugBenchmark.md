# Bug Benchmark Interface

The following document describes the interface of the AbstractBenchmark class - the order of the methods defined represnts the order in which they are ran by Cerberus. A method returning a boolean must indicate whether it was sucessful or not.

```py
def setup_experiment(self, bug_index, container_id, test_all):
```

Prepare the experiment - for example downloading the repository containing it, selecting the exact commit and running any one-time setup scripts.

```py
    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
```

Prepare the experiment for a local run or to go in a container.

```py
    def config(self, bug_index: int, container_id: Optional[str]) -> bool:
```

Configure the experiment - for example running the configure script of a C project.

```py
    def build(self, bug_index: int, container_id: Optional[str]) -> bool:
```

Build the experiment - invoke the build system to check it works.

```py
    def test(self, bug_index: int, container_id: Optional[str]) -> bool:
```

Run a test for the experiment to ensure the vulnerability can be exhibited if the benchmark allows this.

```py
    def verify(self, bug_index: int, container_id: Optional[str]) -> bool:
```

Ensure that there is a repair already known for the vulnerability if the benchmark allows this.

```py
    def save_artefacts(self, dir_info, container_id) -> None:
```

Save the artefacts that are generated.


```py
    def clean(self, exp_dir_path: str, container_id: Optional[str]) -> None:
```

This method is ran to clean up any side-products from the expriment if needed, for example constructing some local files.
