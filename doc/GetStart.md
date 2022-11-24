# Getting Started
Let's walk through a simple example to understand how to use Cerberus. 
We consider the [libtiff project](https://github.com/vadz/libtiff/) from the VulnLoc benchmark.

The bug has instrumentation setup for most of the C program repair tools, thus we can test multiple tools.

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

Extractfix finished. Now I would like to see what exactly happened. Let us run it with debug.

```bash
    cerberus --tool=extractfix --benchmark=vulnloc --bug-index=22 --debug
```

This gave us some patches. Now one can examine them and the logs of each tool.