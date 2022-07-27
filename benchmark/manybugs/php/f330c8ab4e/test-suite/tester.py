#!/usr/bin/python3
import fnmatch
import os
import shutil
import sys
import subprocess

from subprocess import Popen, PIPE

DEVNULL = open(os.devnull, "w")
exp_dir = os.path.abspath(os.path.dirname(os.path.realpath(__file__)))

fail_list = [
    "ext/reflection/tests/traits005.phpt",
    "Zend/tests/bug55825.phpt",
    "Zend/tests/bug55137.phpt",
    "Zend/tests/traits/static_get_called_class.phpt",
    "Zend/tests/traits/static_002.phpt",
]

# Build a list of all the test cases for the program
def build():
    # Find the list of tests used by all ManyBugs PHP scenarios
    with open(exp_dir + "/tests.all.txt", "r") as f:
        all_tests = [t.strip() for t in f]

    # Create test directory
    if not os.path.isdir("tests"):
        os.mkdir("tests")
    for t in all_tests:
        if not os.path.isfile("src/" + t):
            continue
        shutil.copy("src/" + t, "tests/" + str(all_tests.index(t)).zfill(5) + ".phpt")
        file_php = "src/" + t[:-1]
        test_content = []
        if not os.path.isfile(file_php):
            shutil.copy("src/" + t, file_php)
            start_line = 0
            end_line = 0
            with open(file_php, "r", encoding="utf-8", errors="ignore") as test_file:
                test_content = test_file.readlines()
                test_file.seek(0)
                for num, line in enumerate(test_file, 1):
                    if "--FILE-" in line:
                        start_line = num
                    if "--EXPECT" in line:
                        end_line = num
                        break
            with open(file_php, "w+", encoding="utf-8", errors="ignore") as test_file:
                test_file.seek(0)
                test_file.truncate()
                test_file.writelines(test_content[start_line : end_line - 1])
                test_file.write("?>\n")

    # Find the sub-set of tests used by this scenario
    with open(exp_dir + "/tests.indices.txt", "r") as f:
        indices = [int(i.strip()) for i in f]

    tests = set(all_tests[i - 1] for i in indices)

    # Find a list of the failing tests
    with open(exp_dir + "/bug-info/scenario-data.txt", "r") as f:
        lines = [l.strip() for l in f]

    cut_from = next(
        (i for (i, l) in enumerate(lines) if l.startswith("failing tests:"))
    )
    cut_to = next(
        (
            i
            for (i, l) in enumerate(lines)
            if l.startswith("minutes between bug rev and fix rev:")
        )
    )
    failing = set(lines[cut_from + 1 : cut_to - 1])
    if "8d520d6296" in exp_dir:
        failing = set(fail_list)

    # Deduce the set of passing tests
    passing = tests - failing

    # write failing tests to disk
    with open(exp_dir + "/failing.tests.txt", "w") as f:
        for t in sorted(failing):
            f.write("{}\n".format(t))

    with open(exp_dir + "/tests.all.txt.rev", "w") as f:
        rev_list = all_tests.copy()
        rev_list.reverse()
        for t in rev_list:
            f.write("{}\n".format(t))

    # write passing tests to disk
    with open(exp_dir + "/passing.tests.txt", "w") as f:
        for t in sorted(passing):
            f.write("{}\n".format(t))

    shutil.copy(
        "src/" + list(passing)[0], "tests/" + str(len(all_tests)).zfill(5) + ".phpt"
    )
    with open(exp_dir + "/tests/testfile.log", "w") as f:
        f.write("{}\n".format(str(len(all_tests))))
        for t in all_tests:
            f.write("{0}\n{1}\n".format(all_tests.index(t), t))
        f.write("{0}\n{1}\n".format(len(all_tests), list(passing)[0]))


def preexec():
    os.setsid()


def run(identifier, exe=None):
    global exp_dir
    if identifier[0] == "p":
        offset = int(identifier[1:]) - 1
        with open(exp_dir + "/passing.tests.txt") as f:
            test = f.readlines()[offset]
    elif identifier[0] == "n":
        offset = int(identifier[1:]) - 1
        with open(exp_dir + "/failing.tests.txt") as f:
            test = f.readlines()[offset]
    else:
        with open(exp_dir + "/tests.all.txt") as f:
            test = f.readlines()[int(identifier) - 1]
    test = test.strip()

    # determine a time limit (measured in seconds)
    tlim = 60

    print("Running test ({}): {}".format(identifier, test))

    # TODO: Should we stay true to the original ManyBugs and use the compiled executable,
    #       or should we use another (reducing the likelihood of accepting a
    #       plausible but incorrect patch).
    cmd = ["sapi/cli/php", "run-tests.php", "-p", "sapi/cli/php", test]

    with Popen(cmd, stdout=PIPE, stderr=DEVNULL, preexec_fn=preexec) as p:
        try:
            stdout = p.communicate(timeout=tlim)[0]
            try:
                stdout = stdout.decode("ascii")
            except UnicodeDecodeError:
                stdout = stdout.decode("utf-8")
            outcome = stdout.split("\n")[14]
            _, _, outcome = outcome.partition("\r")
            outcome, _, _ = outcome.partition(" ")
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
