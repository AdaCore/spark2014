"""Various set operations on python containers

See unit_testing for a few use cases.
"""

from debug import log_method, log_function

@log_function
def elements_union_gen(iter):
    """Generator for the element union of an iterable

    This is a generalization of the set union to any iterable
    (expect dicts): i.e. it iterates over elements of elements. e.g. for
    {{1, 2}, {3, 4}} it will returns 1, 2, 3, 4.
    If iter is a dict, the keys are dropped and only values are merged.

    PARAMETERS
      iter: the iterable object
    """
    for i in iter:
        if isinstance(iter, dict):
            content = iter[i]
        else:
            content = i

        for e in content:
            if isinstance(content, dict):
                yield content[e]
            else:
                yield e

@log_function
def elements_union(iter):
    """Element union of an iterable

    Same as elements_union_gen, but returns a set instead of a generator.
    """
    return { e for e in elements_union_gen(iter) }

@log_function
def elements_union_0(iter):
    """Extension of elements_union with None as a zero element

    i.e. elements_union_0([Any_Set, None]) == None
    """
    if None in iter:
        return None
    else:
        return elements_union(iter)

@log_function
def elements_union_1(iter):
    """Extension of elements_union with None as an identity element

    i.e. elements_union_1([Any_Set, None]) == Any_Set
    """
    l = [i for i in iter if i is not None]
    if len(l) == 0:
        return None
    else:
        return elements_union(l)

@log_function
def dicts_union(dicts):
    """Union of dict

    Given a list of dicts that have iterables in value, this returns
    a dicts which has:
    * for keys, the union of keys of dicts;
    * as a value for each key, the union of the values for this key
    on each dict.
    """
    return { key : elements_union([o[key] for o in dicts if o.has_key(key)])
             for key in elements_union_gen(o.keys() for o in dicts) }

@log_function
def unit_testing():
    """Unit tests for this module

    The body of this function also provides a few useful examples that
    shows how the functions defined in this module work.
    """
    p1 = {"A" : {11, 12}, "B" : {21, 22}}
    l1 = [[11, 12], [21, 22]]
    assert(elements_union(l1) == {11, 12, 21, 22})
    assert(elements_union(p1) == {11, 12, 21, 22})

    p2 = {"A" : {31, 32}, "C" : {41, 42}}
    p3 = {}
    assert(dicts_union([p1, p2, p3]) == {"A" : {11, 12, 31, 32},
                                         "B" : {21, 22},
                                         "C" : {41, 42}})

    sn = None
    se = set([])
    s1 = {1, 2}
    s2 = {3, 4}
    assert(elements_union_1([sn, se, s1, s2]) == {1, 2, 3, 4})
    assert(elements_union_0([sn, se, s1, s2]) == None)
