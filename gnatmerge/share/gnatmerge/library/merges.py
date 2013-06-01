"""This package provides the basic API to merge results

Consider this package as the entry point of GNATmerge. It defines a class
Merge that should be used to specify a merge operation.
"""

from internal.attributes import lattices
from internal import sets
import entities
import goals

class Merge:
    """Represent a set of merge operations

    ATTRIBUTES
        repository: object repository, of type sets.Objects
        spans: RangeAttribute used to represent sloc spans
    """

    def __init__(self):
        """Constructor."""
        self.repository = sets.Objects()
        self.spans = lattices.RangeAttribute(lattices.SlocBaseType,
                                             "SPAN", "LOW", "HIGH")
        self.slocs = lattices.FreeLatticeAttribute("SLOC",
                                                   lattices.SlocBaseType)
        self.centered_spans = lattices.Product("CENTERED_SPAN",
                                               {self.spans, self.slocs})
        self.goals = {}

    def new_entity(self, name):
        """Create a new entity to be used for this merge"""
        result = entities.Entity(self, name)
        return result

    def loads(self, filename):
        """Load a set of results to be used for this merge"""
        self.repository.loads(filename)

    def new_goal(self, name, entity, value):
        """Set the goal for a given entity

        Any entity of the given type should have a value that is more than
        (or equal to) value.
        """
        result = goals.Goal(entity, value)
        self.goals[name] = result
        return result
