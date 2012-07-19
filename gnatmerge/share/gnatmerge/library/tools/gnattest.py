"""This package provide a way to merge GNATtest outputs with other results
"""
import readers

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
            entity.new_input(reader=readers.ErrorListing("TEST",
                                                         "PASSED",
                                                         "^[0-9]+ tests run"),
                             maps={"OK" : ok,
                                   "KO" : ko})

    def load(self, filename):
        """"Load a file containing results"""
        self.input.load(filename)

