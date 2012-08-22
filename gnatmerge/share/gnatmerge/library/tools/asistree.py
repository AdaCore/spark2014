"""This package provide a way to dump/load ASIS trees for each Ada unit
"""
import readers
from subprocess import Popen
import gpr
import glob

class AsisTree:
    """This class allows to dump ASIS trees

    ASIS trees will be used to apply merges on appropriates source
    entities (e.g. subprograms).
    """

    def __init__(self, entity, asis_kinds):
        """Constructor

        PARAMETERS
          entity      : entity on which level the analysis will be made
                         (e.g. SUBPROGRAM)
          asis_kinds  : list corresponding declaration kinds in the ASIS tree
                         for the given entity. e.g, for entity SUBPROGRAM :
                             ['A_Procedure_Declaration',
                              'A_Procedure_Body_Declaration',
                               ...]})
        """
        # ??? asis_kinds is probably not expressive enough. In particular,
        # it does not allow to match library-level subprograms (and ignore
        # local subprograms).
        self.asis_kinds = asis_kinds
        self.spans = entity.spans
        self.entity = entity
        self.ename = entity.names.name
        self.adts = \
            entity.new_span_input(reader=
                                  readers.AsisTreeReader("SPAN_FRAGMENT",
                                                         self.spans,
                                                         ename=self.ename,
                                                         maps={entity.name :
                                                               asis_kinds}))

    def load(self, filename):
        """Load a file containing results"""
        self.adts.load(filename)

    def run(self):
        """Run GNATProve and load the results
        """
        gpr_filename = gpr.path()
        object_dir = gpr.object_dir()
        Popen(["gnatmake", "-f", "-q", "-g", "-gnatct",
               "-P", gpr_filename]).wait()
        # ??? Use an object sub-directory
        for adt in glob.glob(object_dir + "*.adt"):
            self.load(adt)

        # Contribute names of new elements
        # ??? A bit ad hoc. See if this cannot be
        # clarified in a future clean up.
        object = self.adts.object
        content = object.content()
        for element in content:
            name = object.follow(self.ename, element)
            self.entity.object.touch(name)
