"""This package provides the basic API to interface tools with gnatmerge
"""

from internal.attributes import lattices
from internal.attributes import lattice_ops
from internal import sets

class Entity:
    """Represents a source code entity on which merges should be done

    This class allows to merge results of an entity of a lower level
    (e.g. child) with entities in entities of a higher level. Typically,
    to merge proof results on the subprogram level to the package level,
    one which do:

        m = Merge()
        pck = m.new_entity("PACKAGE")
        subp = pck.new_child("SUBPROGRAM", inherits=m.tristate)

    meaning that the status at the package level will be deduced from the
    status at subprogram level.
    """

    def __init__(self, merge, name):
        """Constructor.

        PARAMETERS
            merge: Merge object to which this entity is attached
            name: name of the entity
            object: Underlying object, of type sets.Object.
        """
        self.name = name
        self.merge = merge
        self.object = self.merge.repository.new_object(name)
        self.object.new_attribute(self.merge.slocs)

    def new_child(self, name, inherits):
        """Create a new child entity

        Create an entity whose instances are always included in
        at most one instance of self, inheriting the specified
        properties.

        PARAMETERS
            name: name of the newly created entity
            inherits: attribute inherited by self from the new child
        """
        child = Entity(self.merge, name)
        child.object.new_attribute(inherits)
        child.object.new_arrow(self.name,
                               lattice_ops.Inclusion(lattice=self.merge.slocs,
                                                     object=self.object))
        self.object.new_arrow(inherits.name,
                              lattice_ops.Join(lattice=inherits,
                                               subobject=child.object,
                                               in_object_key=self.name))

        return child

class Merge:
    """Represent a set of merge operations

    ATTRIBUTES
        repository: object repository, of type sets.Objects
        tristate: Basic PartialOrderAttribute to represent a tool result
            The three possible status are:
            * OK: all sub-entities are OK;
            * KO: all sub-entities are KO;
            * PARTIAL OK: some sub-entities are OK, some are KO
        slocs: RangeAttribute used to represent slocs
    """

    def __init__(self):
        """Constructor."""
        self.repository = sets.Objects()
        self.slocs = lattices.RangeAttribute(lattices.Sloc,
                                             "SLOCS", "LOW", "HIGH")
        self.tristate = lattices.PartialOrderAttribute("STATUS",
                                                       {"OK", "KO"})
        self.tristate.name_meet("PARTIAL OK", {"OK", "KO"})

    def new_entity(self, name):
        """Create a new entity to be used for this merge"""
        result = Entity(self, name)
        return result

    def loads(self, filename):
        """Load a set of results to be used for this merge"""
        self.repository.loads("program.json")
