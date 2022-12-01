# Getting Started

Let's walk through a simple example to understand how to use Cerberus.
We consider the [libtiff project](https://github.com/vadz/libtiff/) from the VulnLoc benchmark as a medium-sized example, which can be followed.

The bug has instrumentation setup for most of the C program repair tools, thus we can test multiple tools in parallel and examine their results.

Let us run some of them - vulnfix, extractfix, f1x and fix2fit.

```bash
    cerberus --tool=vulnfix --benchmark=vulnloc --bug-index=22
```

```bash
    cerberus --tool=f1x --benchmark=vulnloc --bug-index=22
```

```bash
    cerberus --tool=fix2fit --benchmark=vulnloc --bug-index=22
```

```bash
    cerberus --tool=extractfix --benchmark=vulnloc --bug-index=22
```

When running each tool, the output from the run of the tool is stored in the `output/artifacts` folder and the logs in the `output/logs`. Each experiment run has a unique identifier, which can be seen from the first lines of the output of Cerberus. The folder of the artifact contains patches, output of the tool and extra files if defined by the driver.

Extractfix finished. Now I would like to see what exactly happened behind the scenes. Let us run it with debug and see the output.

```bash
    cerberus --tool=extractfix --benchmark=vulnloc --bug-index=22 --debug
```
