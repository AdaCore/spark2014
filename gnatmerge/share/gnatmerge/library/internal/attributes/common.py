"""Common utilities for attributes"""

from internal import sets

class Attribute:
    """Parent of attribute domains

    Children of this class implements an attribute domain
    i.e. represents an attribute as the target of a arrow.
    """

    def eval(self, object, key):
        """Eval the attribute for a given element

        PARAMETERS
          object: set where the element is taken
          key: key of the element in object
        """
        return object.element(key)[self.name]

    def arrow_from_input(self):
        """Build an arrow out an attribute

        Following the resulting arrow means dereferencing the attribute.
        """
        return AttributeArrow(self)

class AttributeArrow(sets.Arrow):
    """Represent an attribute as an arrow

    This class provides the interface of an arrow (i.e. the follow method)
    for an attribute.
    """

    def __init__(self, attribute):
        self.attribute = attribute

    def follow(self, object, key):
        return self.attribute.eval(object, key)

