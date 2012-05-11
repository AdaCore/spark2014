"""Common utilities for attributes"""

import sets

class Attribute:

    def eval(self, object, key):
        return object.element(key)[self.name]

    def arrow_from_input(self):
        return AttributeArrow(self)

class AttributeArrow(sets.Arrow):
    def __init__(self, attribute):
        self.attribute = attribute

    def follow(self, object, key):
        return attribute.eval(object, key)

