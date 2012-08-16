"""This package provides the basic API to manipulate source code entities
"""

from internal.attributes import common
from internal.attributes import lattices
from internal.attributes import lattice_ops
from internal import sets

class Entity:
    """Represents a source code entity on which merges should be done

    This class allows to merge results of entities of a lower level
    (e.g. children) to produce results for entities of a higher
    level. Typically, to merge proof results on the subprogram level to the
    package level, one should do:

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
        # ??? Here spans are under attribute SPAN, not entity.SPAN.
        # And status is under attribute entity.STATUS, and potentially
        # father.STATUS, but not just STATUS. And name is under entity.NAME,
        # NAME and maybe even father.NAME (to be checked). There is clearly
        # a need to improve the homogeneity.
        self.spans = self.merge.spans
        self.object = self.merge.repository.new_object(name)
        if states is not None:
            self.states = states
        else:
            self.states = lattices.OrderedLattice(self.name + ".STATUS")
        self.names = lattices.DiscreteSpace(self.name + ".NAME")
        # ??? should attribute domains know local names? Probably not.
        # If those are supposed to be free from any relation...
        # but they are not. Products is the counterexample. What shall we
        # do? Should products be only relations (arrows), not attributes?
        self.slocs = self.merge.slocs
        self.centered_spans = self.merge.centered_spans
        self.object.new_attribute(self.states)
        self.object.new_attribute(self.names)

        # spans and slocs are not contributed explicitly as attribute.
        # But they are implicitely contributed through centered_spans,
        # which contributes all its projections
        self.object.new_attribute(self.centered_spans)

        # By default, entity.name is a renaming of name
        # ??? Should we do the same for any other attribute?
        # Not clear... We did so for cases where the attribute domain
        # is different for the child and the parent... e.g. TEST.STATUS
        # taking values in {OK, KO}, and SUBPROGRAM.STATUS taking values
        # in {PROVED, NOT PROVED, PARTIALLY PROVED}
        name_renaming = sets.IdentityArrow("NAME")
        self.object.new_arrow(self.names.name, name_renaming)
        cspan_renaming = sets.IdentityArrow("CENTERED_SPAN")
        self.object.new_arrow(self.centered_spans.name, cspan_renaming)

        self.object.join_arrow = {}

    def status_attr_id(self):
        return self.states.name

    def spans_attr_id(self):
        return self.spans.name

    def centered_spans_attr_id(self):
        return self.centered_spans.name

    def names_attr_id(self):
        return self.names.name

    def new_child(self, name, union_name, inclusion, fragments, maps=None):
        """Create a new child entity

        Create an entity whose instances are always included in
        at most one instance of self, inheriting the specified
        properties.

        PARAMETERS
            name: name of the newly created entity
            union_name: name of the attribute where the child's values join
            inclusion: lattice that decides if a child element is into
                       a father element
            fragments: fragment domain for this child
            maps: map describing how its states maps to its father's states.
                  e.g. {"OK" : "PROVED"} means that OK in the child is proved
                  in the parent. If None, use the identity function to map
                  the child's state to the father's state.
        """
        # ??? It would be good to document which attributes, arrows
        # and names are inherited from the father
        child = Entity(self.merge, name, fragments)
        complete_map = maps
        if maps is not None:
            for value in fragments.values:
                if not maps.has_key(value):
                    complete_map[value] = "UNKNOWN"
        inherits = sets.FilteredArrow(child.states, complete_map)
        child.object.new_arrow(self.name,
                               lattice_ops.Inclusion(lattice=inclusion,
                                                     object=self.object))
        child.object.new_arrow(union_name, inherits)
        if self.object.join_arrow.has_key(union_name):
            self.object.join_arrow[union_name].add(child.object)
        else:
            self.object.join_arrow[union_name] = \
              lattice_ops.Join(lattice=self.object.attributes[union_name],
                               subobject=child.object,
                               in_object_key=self.name)
            self.object.new_arrow(union_name,
                                  self.object.join_arrow[union_name])

        return child

    def new_input(self, reader, union_name, inclusion, maps=None):
        child = self.new_child(reader.name, union_name, inclusion,
                               reader.fragments, maps)
        # In the case of Asistree, inclusion is not self.spans, it is
        # the discrete space of names
        child.reader = reader
        return child

    def new_status_input(self, reader, maps=None):
        return self.new_input(reader=reader,
                              union_name=self.status_attr_id(),
                              inclusion=self.spans,
                              maps=maps)

    def new_span_input(self, reader, maps=None):
        return self.new_input(reader=reader,
                              union_name=self.centered_spans_attr_id(),
                              inclusion=self.names,
                              maps=maps)

    def load(self, filename):
        self.reader.load(filename)
        self.object.load(self.reader)
