"""This package provides the basic API to interface tools with gnatmerge
"""

from internal.attributes import common
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
        subp = pck.new_input("SUBPROGRAM", maps={"OK" : "PROVED"})

    meaning that the PROVED status at the package level will be deduced from
    the OK status at subprogram level.

    ATTRIBUTES
      states: state domain for this entity
    """

    def __init__(self, merge, name, states=None):
        """Constructor.

        PARAMETERS
            merge:  Merge object to which this entity is attached
            name:   name of the entity
            states: domain of the status attribute
        """
        self.name = name
        self.merge = merge
        self.object = self.merge.repository.new_object(name)
        self.object.new_attribute(self.merge.slocs)
        if states is not None:
            self.states = states
        else:
            self.states = lattices.PartialOrderAttribute("STATUS")
        self.object.new_attribute(self.states)
        # ??? Double-check that new state values are actually added...

    def new_child(self, name, states, maps):
        """Create a new child entity

        Create an entity whose instances are always included in
        at most one instance of self, inheriting the specified
        properties.

        PARAMETERS
            name: name of the newly created entity
            states: state domain for this child
            maps: map describing how its states maps to its father's states.
                  e.g. {"OK" : "PROVED"} means that OK in the child is proved
                  in the parent.
        """
        child = Entity(self.merge, name, states)
        complete_map = maps
        for value in states.values:
            if not maps.has_key(value):
                complete_map[value] = None
        inherits = sets.FilteredArrow(common.AttributeArrow(child.states),
                                      complete_map)
        child.object.new_arrow(self.name,
                               lattice_ops.Inclusion(lattice=self.merge.slocs,
                                                     object=self.object))
        child.object.new_arrow("STATUS", inherits)
        self.object.new_arrow("STATUS",
                              lattice_ops.Join(lattice=self.states,
                                               subobject=child.object,
                                               in_object_key=self.name))

        return child

    def new_input(self, reader, maps):
        child = self.new_child(reader.name, reader.states, maps)
        child.reader = reader
        return child

    def load(self, filename):
        self.reader.load(filename)
        self.object.load(self.reader)

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
        self.repository.loads(filename)
