""" This provides way to build attribute domains as lattices

Attributes such as sloc ranges or coverage status can naturally be
seen as object of a lattice; this module allow this identification.
"""

from internal.attributes import common
from internal import conversions
from internal import sets
import os.path

class FreeLatticeAttribute(common.Attribute):

    def __init__(self, name, base_type=None):
        self.name = name
        self.M = "MAXIMUM"
        self.empty = set([])
        self.base_type = base_type

    def value_is_in(self, left, right):
        if left == self.M:
            return False
        elif right == self.M:
            return True
        else:
            l = self.maximalize(left)
            r = self.maximalize(right)
            return l.issubset(r)

    def is_in(self, left_object, left_key, right_object, right_key):
        l = self.follow(left_object, left_key)
        r = self.follow(right_object, right_key)
        return self.value_is_in(l, r)

    def value_max(self):
        return self.M

    def empty_set(self):
        return self.empty

    def maximalize(self, value):
        return conversions.to_set(value)

    def minimalize(self, value):
        return value

    def value_join(self, left, right):
        if left == self.M or right == self.M:
            return self.M

        l = self.maximalize(left)
        r = self.maximalize(right)
        result = l.union(l, r)
        return self.minimalize(result)

    def join(self, left_object, left_key, right_object, right_key):
        l = self.follow(left_object, left_key)
        r = self.follow(right_object, right_key)
        return self.value_join(l, r)

    def to_string(self, object):
        if object == self.M:
            return self.M
        elif object == self.empty:
            return "empty"
        elif self.base_type is not None:
            for obj in object:
                o = self.base_type(obj)
            return ", ".join([self.base_type(obj).to_string()
                              for obj in object])
        else:
            return ", ".join([str(obj) for obj in object])

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

    def is_in(self, right):
        if right.abstract_spec is not None:
            if self.abstract_spec == right.abstract_spec:
                return True
            else:
                return not right.is_in(self)
        elif self.abstract_spec is not None:
            if self.abstract_spec == right.abstract_spec:
                return True
            elif self.abstract_spec == "MIN":
                return True
            elif self.abstract_spec == "MAX":
                return False
            else:
                assert(False)

        # ??? Simplistic way to handle different path to the same
        # source file. This was uncovered by L727-003, but is worth
        # making this more robust. It so happen that with project files two
        # Ada source files cannot share the same name; but it is a bit
        # awkard to rely in that.
        if os.path.basename(self.file) != os.path.basename(right.file):
            return False

        if self.line > right.line:
            return False

        if self.line == right.line and self.column > right.column:
            return False

        return True

    def is_extremum(self):
        return False

    def to_string(self):
        return "%s:%s:%s" % (os.path.basename(self.file),
                             self.line, self.column)

    @staticmethod
    def min():
        return "MIN"

    @staticmethod
    def max():
        return "MAX"

class RangeAttribute(FreeLatticeAttribute):

    def __init__(self, base_type, name, low_name, high_name):
        FreeLatticeAttribute.__init__(self, name)
        self.base_type = base_type
        self.low_name = low_name
        self.high_name = high_name
        self.M = {low_name : base_type.min(), high_name : base_type.max()}
        self.empty = set([])

    def value_is_in(self, left, right):

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
                if (right_low.is_in(left_low)
                    and left_high.is_in(right_high)):
                    No_Match = False
                    break

            if No_Match:
                return False

        return True

    def to_string(self, object, key):
        for range in object.follow(self.name, key):
            low = self.base_type(range[self.low_name])
            high = self.base_type(range[self.high_name])
            if low.file == high.file:
                return "%s:%s:%s-%s:%s" % (os.path.basename(low.file),
                                           low.line, low.column,
                                           high.line, high.column)
            else:
                return "%s:%s:%s-%s:%s:%s" % (os.path.basename(low.file),
                                              low.line, low.column,
                                              os.path.basename(high.file),
                                              high.line, high.column)

    def value_join(self, left, right):
        if left == self.M or right == self.M:
            return self.M

        # Simple implementation.
        # We may want to consolidate sloc ranges at some point.
        l = conversions.to_list(left)
        r = conversions.to_list(right)
        return l + r

class PartialOrderAttribute(FreeLatticeAttribute):
    """Represents an attribute domain as a partial order

    ATTRIBUTES
      values: possible values taken by such an attribute
    """

    def __init__(self, name, values=None):
        FreeLatticeAttribute.__init__(self, name)
        self.values = set([])
        self.named_ands = {}
        self.named_ors = {}
        # UNKNOWN is different from None:
        # it marks the case where an entity has been marked by a tool,
        # but the status has not been recognized. It is not that easy to
        # to make this work in the current framework:
        # 1) a or of whatever value X with UNKNOWN should keep UNKNOWN;
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
        value_partial = self.new_value(between)
        self.assume_stronger(maximum, between)
        self.assume_stronger(between, minimum)
        return value_max

    def name_and(self, value, content):
        """Add new value as a and of several pre-existing ones

        PARAMETERS
          name:    unique str used to identify the new value
          content: set that contains the pre-existing values to and
        """
        self.new_value(value)
        for elt in content:
            self.assume_stronger(value, elt)
        self.named_ands[value] = content
        return value

    def name_or(self, value, content):
        """Add new value as a or of several pre-existing ones

        PARAMETERS
          name:    unique str used to identify the new value
          content: set that contains the pre-existing values to or
        """
        self.new_value(value)
        for elt in content:
            self.assume_stronger(elt, value)
        self.named_ors[value] = content
        return value

    def assume_stronger(self, left, right):
        # add left > right
        # ??? The way the partial order works should be clarified a bit.
        self.weaker_classes[left].add(right)

        # compute transitive closure
        for key in self.weaker_classes:
            if left in self.weaker_classes[key]:
                self.weaker_classes[key].add(right)

    def value_is_in(self, left, right):
        l = conversions.to_set(left)
        r = self.maximalize(right)
        return l.issubset(r)

    def maximalize(self, value):
        v = conversions.to_set(value)
        result = v
        for elt in v:
            result = result.union(result, self.weaker_classes[elt])
        for name in self.named_ands:
            if self.named_ands[name].issubset(result):
                result.add(name)
        return result

    def minimalize(self, value):
        v = conversions.to_set(value)
        result = v
        for elt in v:
            result = result.difference(self.weaker_classes[elt])
        for name in self.named_ands:
            if self.named_ands[name].issubset(result):
                result = result.difference(self.named_ands[name])
                result.add(name)

        if len(result) == 1:
            return result.pop()
        else:
            return result

class OrderedLattice(FreeLatticeAttribute):
    """Represents an attribute domain as an ordered lattice

    ATTRIBUTES
      values: possible values taken by such an attribute
    """

    def __init__(self, name, values=None):
        FreeLatticeAttribute.__init__(self, name)
        self.values = set([])
        self.named_joins = {}
        self.partial_order = PartialOrderAttribute(name, values)

        # UNKNOWN is a special status that the order knows
        # already. Add it to the known values of the lattice as
        # well.
        self.inner_classes = {None : set([]), "UNKNOWN" : set([])}
        if values is not None:
            for value in values:
                self.new_value(value)

    def new_value(self, value):
        """Add a new possible value in the attribute domain

        PARAMETERS
          value: unique str used to identify the new value
        """
        self.__new_value(value)
        self.partial_order.new_value(value)
        return value

    def __new_value(self, value):
        """Same as new_value, but without updating the order
        """
        self.values.add(value)
        self.inner_classes[value] = set([])
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
        value_max = self.__new_value(maximum)
        value_min = self.__new_value(minimum)
        value_partial = self.__name_join(between, {value_max, value_min})
        self.partial_order.new_tristate(maximum, minimum, between)
        return value_max

    def name_join(self, value, content):
        """Add new value as a join of several pre-existing ones

        PARAMETERS
          name:    unique str used to identify the new value
          content: set that contains the pre-existing values to join
        """
        self.__name_join(value, content)
        self.partial_order.new_value(value)
        return value

    def __name_join(self, value, content):
        """Same as name_join, but without updating the order
        """
        # ??? Should we provide a public interface for joins, ands, ors?
        # If we want to make complexe things possible, we should...
        # The best way would probably to find a syntax to specify
        # both in the same creation operation. e.g.
        #  self.new_value("PARTIALLY OK", contains="OK, KO",
        #                 spec="KO < PARTIALLY OK < OK")
        # ... Which means that at some point we'll have to check the
        # consistency of the partial order (i.e. no cycle).
        self.new_value(value)
        for elt in content:
            self.assume_outer(value, elt)
        self.named_joins[value] = content
        return value

    def name_or(self, value, content):
        """Specify the order of value as the maximal weakest for a given set

        PARAMETERS
          name:    unique str used to identify the new value
          content: set that contains the pre-existing values to consider
        """
        self.__new_value(value)
        self.partial_order.name_or(value, content)
        return value

    def name_and(self, value, content):
        """Specify the order of value as the minimal strongest for a given set

        PARAMETERS
          name:    unique str used to identify the new value
          content: set that contains the pre-existing values to consider
        """
        self.__new_value(value)
        self.partial_order.name_and(value, content)
        return value

    def assume_outer(self, left, right):
        # add left in right
        self.inner_classes[left].add(right)

        # compute transitive closure
        for key in self.inner_classes:
            if left in self.inner_classes[key]:
                self.inner_classes[key].add(right)

    def value_is_in(self, left, right):
        l = conversions.to_set(left)
        r = self.maximalize(right)
        return l.issubset(r)

    def maximalize(self, value):
        v = conversions.to_set(value)
        result = v
        for elt in v:
            result = result.union(result, self.inner_classes[elt])
        return result

    def minimalize(self, value):
        v = conversions.to_set(value)
        result = v
        for elt in v:
            result = result.difference(self.inner_classes[elt])
        for name in self.named_joins:
            if self.named_joins[name].issubset(result):
                result = result.difference(self.named_joins[name])
                result.add(name)

        if len(result) == 1:
            return result.pop()
        else:
            return result

    def value_less_than(self, left, right):
        return self.partial_order.value_is_in(self.minimalize(left),
                                              self.minimalize(right))

    def less_than(self, left_object, left_key, right_object, right_key):
        l = self.follow(left_object, left_key)
        r = self.follow(right_object, right_key)
        return self.value_less_than(l, r)

class DiscreteSpace(FreeLatticeAttribute):

    def value_is_in(self, left, right):
        if left == self.empty:
            return True
        elif right == self.M:
            return True
        else:
            return left == right

    def maximalize(self, value):
        return value

    def minimalize(self, value):
        return value

    def value_join(self, left, right):
        if left == right:
            return left
        else:
            return self.empty

class Product(FreeLatticeAttribute):

    def __init__(self, name, elements):
        self.elements = elements
        self.name = name
        self.M = {}
        self.empty = {}
        for e in elements:
            self.M[e.name] = e.value_max()
            self.empty[e.name] = e.empty_set()

    def value_is_in(self, left, right):
        for e in self.elements:
            if not e.value_is_in(left[e.name], right[e.name]):
                return False
        return True

    def maximalize(self, value):
        return value

    def minimalize(self, value):
        return value

    def value_join(self, left, right):
        result = {}
        for e in self.elements:
            result[e.name] = e.value_join(left[e.name], right[e.name])
        return result

    def project(self, name, object, key):
        return self.follow(object, key)[name]

    def contribute_arrows(self, object):
        attr_arrow = sets.AttributeArrow(self.name)
        object.new_arrow(self.name, attr_arrow)
        for e in self.elements:
            object.new_arrow(e.name, sets.ProjectionArrow(e.name, self))
