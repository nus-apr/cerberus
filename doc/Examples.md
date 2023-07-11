# Example Usage

In this document we provide examples of how to use Cerberus with prepared test cases to elaborate the capabilities of Cerberus. Following details explain the test-cases we provide in our repository. Please take a look at the page Getting Started to understand how to use Cerberus.

```bash
   cerberus -task repair --tool=extractfix --benchmark=vulnloc --bug-index=1
```

This is one of the most basic commands -running ExtractFix on the first vulnerability in Vulnloc.

```bash
   cerberus -task repair --tool=extractfix --benchmark=vulnloc --bug-index=1 --debug
```

Simarly we run the tool with debug mode on.

```bash
   cerberus -task repair --tool=extractfix --benchmark=vulnloc --bug-index-list=1-2,5,10-20
```

Now let us batch more bugs - the first two bugs, the fifth bug and then from the 10th to the 20th bug.

```bash
   cerberus -task repair --tool=prophet --benchmark=vulnloc --bug-index-list=1-2,5,10-20 --local
```

Let's assume that we want to run the experiments locally, only thing that needs to be added is the --local and one can ensure that prophet is locally accessible.

```bash
   cerberus -task repair --tool=prophet --benchmark=vulnloc --bug-index=4 --conf=C4
```

The experiment can also be ran with a different configuration profile.

```bash
   cerberus -task repair --tool=prophet --benchmark=vulnloc --bug-index=4 --setup-only
```

Or until the setup stage only.

```bash
   cerberus -task repair --tool=prophet --benchmark=vulnloc --bug-index=4 --instrument-only
```

Or until the instrumentation stage only.

```bash
   cerberus -task repair --tool=prophet --benchmark=vulnloc --bug-index=4 --rebuild-exp
```

If needed one can also rebuild the experiment image.
