"""This package provides the basic API to merge results

Consider this package as the entry point of GNATMerge. It defines a class
Merge that should be used to specify a merge operation.
"""

from internal.attributes import lattices
from internal import sets
import entities

class Merge:
    """Represent a set of merge operations

    ATTRIBUTES
        repository: object repository, of type sets.Objects
        slocs: RangeAttribute used to represent slocs
    """

    def __init__(self):
        """Constructor."""
        self.repository = sets.Objects()
        self.slocs = lattices.RangeAttribute(lattices.Sloc,
                                             "SLOCS", "LOW", "HIGH")
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
        self.goals[name] = {"entity" : entity, "value" : value}

    def goal_reached(self, name):
        entity = self.goals[name]["entity"]
        goal = self.goals[name]["value"]
        for elt in entity.object.content():
            value = entity.object.follow(entity.status_name(), elt)
            attribute = entity.object.attributes[entity.status_name()]
            if attribute.value_less_than(goal, value):
                print "REACHED : %s : %s" % (str(elt), str(value))
