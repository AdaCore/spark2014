""" This provides way to build attribute domains as lattices

Attributes such as sloc ranges or coverage status can naturally be
seen as object of a lattice; this module allow this identification.
"""

import common
import conversions

class RangeAttribute(common.Attribute):

    def __init__(self, name, low_name, high_name):
        self.name = name
        self.low_name = low_name
        self.high_name = high_name
        # ??? silly implementation for the maximum value,
        # just for the prototype.
        self.M = {"LOW" : 0, "HIGH" : 90000}

    def value_less_than(self, left, right):
        # left <= right iff left's range is in right'range
        return (right[self.low_name] <= left[self.low_name]
                and left[self.high_name] <= right[self.high_name])

    def less_than(self, left_object, left_key, right_object, right_key):
        return self.value_less_than(left_object.element(left_key)[self.name],
                                    right_object.element(right_key)[self.name])

    def value_max(self):
        return self.M

class PartialOrderAttribute(common.Attribute):
    def __init__(self, name, values):
        self.name = name
        self.values = values
        self.weaker_classes = {None : []}
        for value in values:
            self.weaker_classes[value] = {None,}

    def assume_stronger(self, left, right):
        # add left > right
        # ??? The way the partial order works should be clarified a bit.
        self.weaker_classes[left].add(right)

        # compute transitive closure
        for key in self.weaker_classes:
            if left in self.weaker_classes[key]:
                self.weaker_classes[key].add(right)

    def value_less_than(self, left, right):
        r = conversions.to_set(right)
        return r in to_set(self.weaker_classes[left])

    def less_than(self, left_object, left_key, right_object, right_key):
        return self.value_less_than(left_object.element(left_key)[self.name],
                                    right_object.element(right_key)[self.name])

    def empty_set(self):
        return None

    def maximalize(self, value):
        v = conversions.to_set(value)
        result = v
        for elt in v:
            result = result.union(result, self.weaker_classes[elt])
        return result

    def minimalize(self, value):
        v = conversions.to_set(value)
        result = v
        for elt in v:
            result = result.difference(self.weaker_classes[elt])
        if len(result) == 1:
            return result.pop()
        else:
            return result

    def value_join(self, left, right):
        l = self.maximalize(left)
        r = self.maximalize(right)
        result = l.union(l, r)
        return self.minimalize(result)

    def join(self, left_object, left_key, right_object, right_key):
        return self.value_join(left_object.element(left_key)[self.name],
                               right_object.element(right_key)[self.name])

