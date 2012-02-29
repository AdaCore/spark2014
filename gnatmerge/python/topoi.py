
import conversions

class Classifier:
    def __init__(self, partial_order):
        self.po = partial_order

    def canonicalize(self, object):
        object = conversions.to_set(object)
        for elt in object:
            if self.po.weaker_classes.has_key(elt):
                object = self.join(object, self.po.weaker_classes[elt])
        return object

    def join(self, left, right):
        return left.union(right)

    def meet(self, left, right):
        return left.intersection(right)

    def equal(self, left, right):
        l = self.canonicalize(left)
        r = self.canonicalize(right)
        return l == r

    def ge(self, left, right):
        return self.equal(right, self.meet(left, right))

    def le(self, left, right):
        return self.ge(right, left)

    def gt(self, left, right):
        return not self.equal(left, right) and self.ge(left, right)

    def lt(self, left, right):
        return self.gt(right, left)

class Subobjects:
    def __init__(self, classifier, content):
        self.classifier = classifier
        self.minimum = self.canonicalize(content)

    def subobject(self, content):
        return self.join(self.canonicalize(content), self.minimum)

    def canonicalize(self, content):
        canonicalized = {}
        for elt in content:
            canonicalized[elt] = self.classifier.canonicalize(content[elt])
        return canonicalized

    def join(self, left, right):
        result = {}
        for elt in left:
            if right.has_key(elt):
                result[elt] = self.classifier.join(left[elt], right[elt])
            else:
                result[elt] = left[elt]
        for elt in right:
            if not left.has_key(elt):
                result[elt] = right[elt]
        return result

    def meet(self, left,right):
        # Not implemented
        pass

    def imply(self, left,right):
        # Not implemented
        pass

    def complement(self, op):
        # Not implemented
        pass


def canonicalize(e):
    if e is None:
        return {}
    elif isinstance(e, dict):
        result = {}
        for key in e:
            result[key] = canonicalize(e[key])
        return result
    elif isinstance(e, basestring):
        return { e : None }
    elif isinstance(e, (list,tuple,set)):
        result = {}
        for key in e:
            result += { key : None }
    else:
        return { e : None }

class Realization:
    def __init__(self, sketch, content):
        self.sketch = sketch
        self.minimum = canonicalize(content)

    def subobject(self, content):
        return canonicalize(content)

    def join(self, left, right):
        result = {}
        for elt in left:
            if right.has_key(elt):
                result[elt] = self.join_element(elt, left[elt], right[elt])
            else:
                result[elt] = left[elt]
        for elt in right:
            if not left.has_key(elt):
                result[elt] = right[elt]
        return result

    def expand_key(self, key, elt):
        return elt

    def join_element(self, x, left, right):
        result = {}
        for key in left:
            right = self.expand_key(key, right)
            if right.has_key(key):
                # ??? Have a callback to properly merge the result?
                # + special case for "Max" or "Min" ?
                assert(left[key] == right[key])
            else:
                result[key] = left[key]
        for key in right:
            result[key] = right[key]
        return result

    def meet(self, left, right):
        pass

    def complement(self, op):
        # Not implemented
        # ??? Actually, the complement will not be of much use
        # in our context: as all considered subobjects contains
        # all subprograms, their complement is the same for all:
        # the empty subobject...
        pass

    def imply(self, left,right):
        # Not implemented
        pass


############################################################################
# A few tests...
if __name__ == "__main__":
    import sketches

    s1 = sketches.PartialOrder({"PROVED", "TESTED", "OK", "SUBPROGRAM"})
    test_1 = Classifier(s1)

    t1 = {"PROVED", "SUBPROGRAM"}
    t2 = {"TESTED", "SUBPROGRAM"}
    m = test_1.meet(t1, t2)
    j = test_1.join(t1, t2)
    for i in [t1, t2, m, j]:
        assert(test_1.equal(i, i))
    assert(not test_1.equal(t1, t2))
    assert(test_1.equal(j, {'TESTED', 'PROVED', 'SUBPROGRAM'}))
    assert(test_1.equal(j, {'TESTED', 'SUBPROGRAM', 'PROVED'}))
    assert(test_1.equal(j, {'PROVED', 'SUBPROGRAM', 'TESTED'}))
    assert(test_1.equal(j, {'PROVED', 'TESTED', 'SUBPROGRAM'}))
    assert(test_1.equal(j, {'SUBPROGRAM', 'TESTED', 'PROVED'}))
    assert(test_1.equal(j, {'SUBPROGRAM', 'PROVED', 'TESTED'}))
    assert(test_1.equal(m, {'SUBPROGRAM'}))
    assert(test_1.ge(j, t2))
    assert(test_1.gt(j, t1))
    assert(test_1.ge(j, j))
    assert(not test_1.gt(j, j))
    assert(test_1.le(m, t2))
    assert(test_1.lt(m, t1))
    assert(test_1.le(m, m))
    assert(not test_1.lt(m, m))

    s1.assume_stronger("PROVED", "OK")
    s1.assume_stronger("TESTED", "OK")
    s1.assume_stronger("OK", "SUBPROGRAM")
    test_1 = Classifier(s1)

    t1 = test_1.canonicalize({"PROVED"})
    t2 = test_1.canonicalize({"TESTED"})
    m = test_1.meet(t1, t2)
    j = test_1.join(t1, t2)
    for i in [t1, t2, m, j]:
       assert(test_1.equal(i, i))
       assert("SUBPROGRAM" in i)
       assert("OK" in i)
    for i in [t1, j]:
        assert("PROVED" in i)
    for i in [t2, j]:
        assert("TESTED" in i)

