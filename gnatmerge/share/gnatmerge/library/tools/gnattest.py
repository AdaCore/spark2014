"""This package provide a way to merge GNATtest outputs with other results
"""
import readers
from subprocess import Popen
import gpr

class GNATtest:
    """This class allows to feed GNATtest results into GNATmerge
    """

    def __init__(self, entity,
                 ok="TEST PASSED", ko="TEST FAILED",
                 between="TEST PASSED PARTIALLY"):
        """Constructor

        PARAMETERS
          entity : entity on which level the analysis will be made
          ok     : status name indicating that an entity as been marked
                   as ok by the tool
          ko     : complement of ko
          between: status for the case where some part are ok, and some are not
        """
        self.ok = ok
        self.ko = ko
        self.between = between
        entity.states.new_tristate(self.ok, self.ko, self.between)
        self.input = \
            entity.new_status_input(reader=
                                    readers.ErrorListing("TEST",
                                                         "PASSED",
                                                         "^[0-9]+ tests run"),
                                    maps={"OK" : ok,
                                          "KO" : ko})

    def load(self, filename):
        """Load a file containing results"""
        self.input.load(filename)

    def run(self):
        """Run tests and load the results
        """
        gpr_filename = gpr.path()
        object_dir = gpr.object_dir()
        harness_dir = object_dir + "/gnattest/harness"
        test_runner = harness_dir + "/test_runner"
        results = object_dir + "/gnattest.mrg"
        # ??? Log any tool output.
        Popen(["gnattest", "-P", gpr_filename, "-q"]).wait()
        Popen(["gnatmake",
               "-P", harness_dir + "/test_driver.gpr", "-q"]).wait()
        with open(results, 'w') as fd:
            p = Popen([test_runner], stdout=fd)
            p.wait()
        self.load(results)
