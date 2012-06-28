"""Common utilities for attributes"""

from internal import sets

class Attribute(sets.Arrow):
    """Parent of attribute domains

    Children of this class implements an attribute domain
    i.e. represents an attribute as the target of a arrow.
    """

    def follow(self, object, key):
        """Eval the attribute for a given element

        PARAMETERS
          object: set where the element is taken
          key: key of the element in object
        """
        return object.follow(self.name, key)
