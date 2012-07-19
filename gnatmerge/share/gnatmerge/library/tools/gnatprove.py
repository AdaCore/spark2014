"""This package provide a way to merge GNATprove outputs with other results
"""
import readers
from subprocess import Popen

class GNATprove:
    """This class allows to feed GNATprove results into GNATmerge
    """

    def __init__(self, entity,
                 ok="PROVED", ko="NOT PROVED", between="PARTIALLY PROVED"):
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
        self.vcs = \
            entity.new_input(reader=readers.ErrorListing("VC",
                                                         ignore_pattern="^$"),
                             maps={"OK" : ok,
                                   "KO" : ko,
                                   "PARTIAL OK" : between})

    def load(self, filename):
        """"Load a file containing results"""
        self.vcs.load(filename)

    def run(self, gpr_filename):
        results="gnatprove.mrg"
        # ??? Get this info from the gpr file.
        with open(results, 'w') as fd:
            p = Popen(["gnatprove",
                       "-q",
                       "--mode=prove",
                       "--report=all",
                       "-P", gpr_filename],
                      stdout=fd)
            p.wait()
        self.load(results)
