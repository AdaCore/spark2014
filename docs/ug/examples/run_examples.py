#! /usr/bin/env python

from e3.testsuite import Testsuite
from e3.testsuite.testcase_finder import TestFinder, ParsedTest
from e3.testsuite.driver.diff import DiffTestDriver
import glob
import os
import os.path
import sys


class ExamplesTestFinder(TestFinder):
    """Include all direct subdirs"""

    def __init__(self, driver_cls, root_dir):
        """
        Initialize a ExamplesTestFinder instance.

        :param e3.testsuite.driver.TestDriver driver_cls: TestDriver subclass
            to use for all tests that are found.
        """
        self.driver_cls = driver_cls
        self.root_dir = root_dir

    def probe(self, testsuite, dirpath, dirnames, filenames):
        parent_name = os.path.dirname(dirpath)
        testname = os.path.basename(dirpath)
        # If the dir is not a direct subdir of <root_dir/tests>, skip it
        if (os.path.basename(parent_name) != "tests" or
                os.path.dirname(parent_name) != self.root_dir):
            return None
        return ParsedTest(testname, self.driver_cls, {}, dirpath)


class ExamplesTestDriver(DiffTestDriver):

    copy_test_directory = True

    def run(self):
        pattern = os.path.join(self.test_env["working_dir"], "*.gpr")
        gprfiles = glob.glob(pattern)
        assert(len(gprfiles) == 1)
        cmd = ["gnatprove",
               "-P", gprfiles[0],
               "-f", "-q", "-j0",
               "--level=2",
               "--steps=100",
               "--timeout=60"]
        self.shell(cmd, catch_error=False)


class ExamplesTestsuite(Testsuite):

    @property
    def test_finders(self):
        return [ExamplesTestFinder(ExamplesTestDriver,
                                   self.root_dir)]

    def set_up(self):
        self.env.rewrite_baselines = True


if __name__ == "__main__":
    sys.exit(ExamplesTestsuite().testsuite_main())
