"""Common utilities for attributes"""

from internal import sets

class Attribute:
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
        # Note that an attribute never knows how
        # to dereference a key and execute an
        # arrow: that's the object that has this knowledge.
        # Attribute only know about how to do maths on
        # the resulting values. So this method is really
        # not much more than a shortcut.
        return object.follow(self.name, key)

    def contribute_arrows(self, object):
        object.new_arrow(self.name, sets.AttributeArrow(self.name))

class RenamedAttribute(Attribute):

    def __init__(self, name, attribute):
        self.attribute = attribute
        self.name = name

    def follow(self, object, key):
        return self.attribute.follow(object, key)
