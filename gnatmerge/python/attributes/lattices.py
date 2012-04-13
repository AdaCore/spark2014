""" This provides way to build attribute domains as lattices

Attributes such as sloc ranges or coverage status can naturally be
seen as object of a lattice; this module allow this identification.
"""

import common
import conversions

class Sloc:
    def __init__(self, spec):
        if spec == "MIN" or spec == "MAX":
            self.abstract_spec = spec
        else:
            self.abstract_spec = None
            parts = spec.split(":")
            self.file = parts[0]
            self.line = int(parts[1])
            try:
                self.column = int(parts[2])
            except:
                self.column = 0

    def less_than(self, right):
        if right.abstract_spec is not None:
            if self.abstract_spec == right.abstract_spec:
                return True
            else:
                return not right.less_than(self)
        elif self.abstract_spec is not None:
            if self.abstract_spec == right.abstract_spec:
                return True
            elif self.abstract_spec == "MIN":
                return True
            elif self.abstract_spec == "MAX":
                return False
            else:
                assert(False)

        if self.file != right.file:
            return False

        if self.line > right.line:
            return False

        if self.line == right.line and self.column > right.line:
            return False

        return True

    def is_extremum(self):
        return False

    @staticmethod
    def min():
        return "MIN"

    @staticmethod
    def max():
        return "MAX"

class RangeAttribute(common.Attribute):

    def __init__(self, base_type, name, low_name, high_name):
        self.base_type = base_type
        self.name = name
        self.low_name = low_name
        self.high_name = high_name
        # ??? silly implementation for the maximum value,
        # just for the prototype.
        self.M = {low_name : base_type.min(), high_name : base_type.max()}

    def value_less_than(self, left, right):

        # ??? quick and dirty implementation for now.  Would be good
        # to fully order slocs in order to improve efficiency at some
        # point.

        for left_range in conversions.to_list(left):
            left_low = Sloc(left_range[self.low_name])
            left_high = Sloc(left_range[self.high_name])
            No_Match = True
            for right_range in conversions.to_list(right):
                right_low = Sloc(right_range[self.low_name])
                right_high = Sloc(right_range[self.high_name])
                # left <= right iff left's range is in right'range
                if (right_low.less_than(left_low)
                    and left_high.less_than(right_high)):
                    No_Match = False
                    break

            if No_Match:
                return False

        return True

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

