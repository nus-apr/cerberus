#!/usr/bin/python3
import fnmatch
import os
import sys
import subprocess

from subprocess import Popen, PIPE

DEVNULL = open(os.devnull, 'w')


# Build a list of all the test cases for the program
def build():
    # Find the list of tests used by all ManyBugs PHP scenarios
    with open("/experiment/tests.all.txt", "r") as f:
        all_tests = [t.strip() for t in f]

    # Find the sub-set of tests used by this scenario
    with open("/experiment/tests.indices.txt", "r") as f:
        indices = [int(i.strip()) for i in f]

    tests = set(all_tests[i - 1] for i in indices)

    # Find a list of the failing tests
    with open("/experiment/bug-info/scenario-data.txt", "r") as f:
        lines = [l.strip() for l in f]

    cut_from = \
        next((i for (i, l) in enumerate(lines) if l.startswith("failing tests:")))
    cut_to = \
        next((i for (i, l) in enumerate(lines) if l.startswith("minutes between bug rev and fix rev:")))
    failing = set(lines[cut_from + 1:cut_to - 1])

    # Deduce the set of passing tests
    passing = tests - failing

    # write failing tests to disk
    with open("/experiment/failing.tests.txt", "w") as f:
        for t in sorted(failing):
            f.write("{}\n".format(t))

    # write passing tests to disk
    with open("/experiment/passing.tests.txt", "w") as f:
        for t in sorted(passing):
            f.write("{}\n".format(t))


def preexec():
    os.setsid()


def run(identifier, exe=None):
    offset = int(identifier[1:]) - 1
    if identifier[0] == "p":
        with open("/experiment/passing.tests.txt") as f:
            test = f.readlines()[offset]
    elif identifier[0] == "n":
        with open("/experiment/failing.tests.txt") as f:
            test = f.readlines()[offset]
    test = test.strip()

    # determine a time limit (measured in seconds)
    tlim = 60

    print("Running test ({}): {}".format(identifier, test))

    # TODO: Should we stay true to the original ManyBugs and use the compiled executable,
    #       or should we use another (reducing the likelihood of accepting a
    #       plausible but incorrect patch).
    cmd = ["sapi/cli/php", "run-tests.php", "-p", "sapi/cli/php", test]

    with Popen(cmd, stdout=PIPE, stderr=DEVNULL, preexec_fn=preexec, cwd="/experiment/src") as p:
        try:
            stdout = p.communicate(timeout=tlim)[0]
            try:
                stdout = stdout.decode("ascii")
            except UnicodeDecodeError:
                stdout = stdout.decode("utf-8")
            outcome = stdout.split("\n")[14]
            _, _, outcome = outcome.partition('\r')
            outcome, _, _ = outcome.partition(' ')
            return outcome in ["PASS", "SKIP"]

        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            return False

        except:
            return False

    return False


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "build":
        build()
    elif cmd == "run":
        if run(*sys.argv[2:]):
            print("PASS")
            sys.exit(0)
        else:
            print("FAIL")
            sys.exit(1)