""" This provides way to build attribute domains as lattices

Attributes such as sloc ranges or coverage status can naturally be
seen as object of a lattice; this module allow this identification.
"""

from internal.attributes import common
from internal import conversions

class SlocBaseType:
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

    def to_string(self, value):
        return "%s:%s:%s" % (self.file, self.file, self.column)

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
            left_low = self.base_type(left_range[self.low_name])
            left_high = self.base_type(left_range[self.high_name])
            No_Match = True
            for right_range in conversions.to_list(right):
                right_low = self.base_type(right_range[self.low_name])
                right_high = self.base_type(right_range[self.high_name])
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

    def to_string(self, object, key):
        for range in object.follow(self.name, key):
            low = self.base_type(range[self.low_name])
            high = self.base_type(range[self.high_name])
            if low.file == high.file:
                return "%s:%s:%s-%s:%s" % (low.file, low.line, low.column,
                                           high.line, high.column)
            else:
                return "%s:%s:%s-%s:%s:%s" % (low.file,
                                              low.line, low.column,
                                              high.file,
                                              high.line, high.column)


class PartialOrderAttribute(common.Attribute):
    """Represents an attribute domain as a partial order

    ATTRIBUTES
      values: possible values taken by such an attribute
    """

    def __init__(self, name, values=None):
        self.name = name
        self.values = set([])
        self.named_meets = {}
        self.named_joins = {}
        # UNKNOWN is different from None:
        # it marks the case where an entity has been marked by a tool,
        # but the status has not been recognized. It is not that easy to
        # to make this work in the current framework:
        # 1) a join of whatever value X with UNKNOWN should keep UNKNOWN;
        #    so UNKNOWN should not be inferior to X;
        # 2) UNKNOWN does not allow to reach whatever goal G;
        #    so UNKNOWN should not be superior to X.
        # ??? should any goal be considered as reached if UNKNOWN appears
        # in the result? Probably not. In which case we may have some
        # special treatment for it...
        self.weaker_classes = {None : set([]), "UNKNOWN" : set([])}
        if values is not None:
            for value in values:
                self.new_value(value)

    def new_value(self, value):
        """Add a new possible value in the attribute domain

        PARAMETERS
          value: unique str used to identify the new value
        """
        self.values.add(value)
        self.weaker_classes[value] = set([])
        return value

    def new_tristate(self, maximum, minimum=None, between=None):
        """Add a tristate value in the attribute domain

        This adds three new values to be used to represent a tristate
        e.g PROVED, NOT PROVED, PARTIALLY PROVED. Returns the maximum
        value (e.g. PROVED).

        PARAMETERS
           maximum: unique str used to identify a new value in the
                    attribute domain that stand for the maximum.
           minimum: same as maximum, but for the minimum. If not
                    specified, will be "NOT maximum".
           between: unique str used to identify a value in between.
                    If not specified, will be "PARTIALLY maximum".
        """
        if minimum is None:
            minimum = "NOT " + maximum
        if between is None:
            between = "PARTIALLY " + maximum
        value_max = self.new_value(maximum)
        value_min = self.new_value(minimum)
        value_partial = self.name_and(between, {value_max, value_min})
        return value_max

    def name_and(self, value, content):
        """Add new value as a meet of several pre-existing ones

        PARAMETERS
          name:    unique str used to identify the new value
          content: set that contains the pre-existing values to meet
        """
        self.new_value(value)
        for elt in content:
            self.assume_stronger(value, elt)
        self.named_meets[value] = content
        return value

    def name_or(self, value, content):
        """Add new value as a join of several pre-existing ones

        PARAMETERS
          name:    unique str used to identify the new value
          content: set that contains the pre-existing values to meet
        """
        self.new_value(value)
        for elt in content:
            self.assume_stronger(elt, value)
        self.named_joins[value] = content
        return value

    def assume_stronger(self, left, right):
        # add left > right
        # ??? The way the partial order works should be clarified a bit.
        self.weaker_classes[left].add(right)

        # compute transitive closure
        for key in self.weaker_classes:
            if left in self.weaker_classes[key]:
                self.weaker_classes[key].add(right)

    def value_less_than(self, left, right):
        l = conversions.to_set(left)
        r = self.maximalize(right)
        return l.issubset(r)

    def less_than(self, left_object, left_key, right_object, right_key):
        return self.value_less_than(left_object.element(left_key)[self.name],
                                    right_object.element(right_key)[self.name])

    def empty_set(self):
        return set([])

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
        for name in self.named_meets:
            if self.named_meets[name].issubset(result):
                result = result.difference(self.named_meets[name])
                result.add(name)

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


