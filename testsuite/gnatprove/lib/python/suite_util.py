"""Utilities shared by testsuite maintenance scripts."""

import os
import yaml

TEST_DIRS = ["tests", "internal", "sparklib"]


def find_test_dir(name):
    """Return the directory of test NAME, or None if not found."""
    for d in TEST_DIRS:
        path = os.path.join(d, name)
        if os.path.exists(path):
            return path
    return None


def read_write_yaml(testname, fn):
    """Apply FN to the test.yaml data of TESTNAME and write it back."""
    path = find_test_dir(testname)
    if path is None:
        print(f"Unable to find test dir to modify yaml file for {testname}")
        return
    yamlfile = os.path.join(path, "test.yaml")
    if not os.path.exists(yamlfile):
        data = {}
    else:
        with open(yamlfile, "r") as f:
            data = yaml.safe_load(f)
    data = fn(data)
    if not data:
        os.remove(yamlfile)
    else:
        with open(yamlfile, "w") as f:
            yaml.dump(data, f)


def is_large(name):
    """Return True if test NAME is marked as large in test.yaml."""
    path = find_test_dir(name)
    if path is None:
        return None
    yamlfile = os.path.join(path, "test.yaml")
    if not os.path.exists(yamlfile):
        return False
    with open(yamlfile) as f:
        data = yaml.safe_load(f)
    return bool(data.get("large", False))


def make_large(testname):
    def set_large(d):
        result = dict(d)
        result["large"] = True
        return result

    print(f"Moving {testname} to large")
    read_write_yaml(testname, set_large)


def make_nonlarge(testname):
    def erase_large(d):
        result = dict(d)
        del result["large"]
        return result

    print(f"Removing {testname} from large")
    read_write_yaml(testname, erase_large)
