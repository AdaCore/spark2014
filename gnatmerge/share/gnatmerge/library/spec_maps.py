"""Merges from one status space to another

This module provide ways to map the power set of status space to an
other status space; e.g. the status space of VCs ("VC_PROVED",
"VC_NOT_PROVED") to the status space of an enclosing source entity
(e.g. "FULLY PROVED", "NOT PROVED", "PARTIALLY PROVED"). The map is
expressed using merge specifications (as defined in module merge_specs).

See unit_testing for a few use cases.
"""

from merge_specs import MergeSpec
from status import MergeStatusFactory, new_model, add_to_model
from elements import elements_union
from debug import log_method, log_function
from utils import iterable

class SpecMap:
    """Same as MergeSpec, but for several named expressions
    """

    @log_method
    def __init__(self, map=None):
        """Constructor

        map contains pairs <name> : <expression> that records the
        named expressions that are to be handled in that object.
        """
        self.map = {}

        if map is not None:
            self.add(map)

    @log_method
    def add(self, map):
        """Add entries to map

        PARAMETERS
          map: Same as in constructor
        """
        for key in map:
            assert(key not in self.map)
            self.map[key] = MergeSpec(map[key],
                                      MergeStatusFactory(),
                                      name=key)

    @log_method
    def add_atoms(self, atoms):
        for atom in iterable(atoms):
            self.add({atom : "some %s" % atom})

    @log_method
    def apply(self, model):
        """Model morphism

        Same as MergeSpec.apply, but for several named expressions; return
        a model whose entries are the name of all expressions, and whose
        proofs/counterexamples are the proofs/counterexamples of each
        corresponding entry.
        """
        l = {key : self.map[key].apply(model) for key in self.map}
        return {True  : {key : l[key][True][key] for key in l},
                False : {key : l[key][False][key] for key in l}}

@log_function
def unit_testing():
    """Unit tests for this module

    The body of this function also provides a few useful examples that
    shows how the functions defined in this module work.
    """
    from messages import Message

    m1 = Message(name ="VC1", status="OK", sloc="p.adb:1:1",
                 message="overflow check proved")
    m2 = Message(name ="VC2", status="KO", sloc="p.adb:2:2",
                 message="overflow check not proved")
    m3 = Message(name ="VC3", status="OK", sloc="p.adb:3:3",
                 message="assertion proved")
    m4 = Message(name ="VC4", status="KO", sloc="p.adb:4:4",
                 message="assertion not proved")

    spec_map = SpecMap({"PROVED"           : "some OK and no   KO",
                        "PARTIALLY PROVED" : "some OK",
                        "NOT PROVED"       : "no   OK and some KO",
                        "NO VCS"           : "no   OK and no KO"})
    spec_map.add({"OK SO FAR"        : "no KO",
                  "STRICTLY PARTIAL" : "some OK and some KO"})

    model = new_model()
    assert(spec_map.apply(model) == {
        True   : {"NO VCS"           : set([]),
                  "OK SO FAR"        : set([]),
                  "PROVED"           : None,
                  "PARTIALLY PROVED" : None,
                  "STRICTLY PARTIAL" : None,
                  "NOT PROVED"       : None},
        False  : {"NO VCS"           : None,
                  "OK SO FAR"        : None,
                  "PROVED"           : set([]),
                  "PARTIALLY PROVED" : set([]),
                  "STRICTLY PARTIAL" : set([]),
                  "NOT PROVED"       : set([])}})

    add_to_model(model, "OK", m1)
    assert(spec_map.apply(model) == {
        True   : {"NO VCS"           : None,
                  "OK SO FAR"        : set([]),
                  "PROVED"           : {m1},
                  "PARTIALLY PROVED" : {m1},
                  "STRICTLY PARTIAL" : None,
                  "NOT PROVED"       : None},
        False  : {"NO VCS"           : {m1},
                  "OK SO FAR"        : None,
                  "PROVED"           : None,
                  "PARTIALLY PROVED" : None,
                  "STRICTLY PARTIAL" : set([]),
                  "NOT PROVED"       : {m1}}})

    add_to_model(model, "KO", m2)
    assert(spec_map.apply(model) == {
        True   : {"NO VCS"           : None,
                  "OK SO FAR"        : None,
                  "PROVED"           : None,
                  "PARTIALLY PROVED" : {m1},
                  "STRICTLY PARTIAL" : {m1, m2},
                  "NOT PROVED"       : None},
        False  : {"NO VCS"           : {m1, m2},
                  "OK SO FAR"        : {m2},
                  "PROVED"           : {m2},
                  "PARTIALLY PROVED" : None,
                  "STRICTLY PARTIAL" : None,
                  "NOT PROVED"       : {m1}}})

    model = new_model()
    add_to_model(model, "KO", m2)
    add_to_model(model, "KO", m4)
    assert(spec_map.apply(model) == {
        True   : {"NO VCS"           : None,
                  "OK SO FAR"        : None,
                  "PROVED"           : None,
                  "PARTIALLY PROVED" : None,
                  "STRICTLY PARTIAL" : None,
                  "NOT PROVED"       : {m2, m4}},
        False  : {"NO VCS"           : {m2, m4},
                  "OK SO FAR"        : {m2, m4},
                  "PROVED"           : {m2, m4},
                  "PARTIALLY PROVED" : set([]),
                  "STRICTLY PARTIAL" : set([]),
                  "NOT PROVED"       : None}})

    atomic_spec = SpecMap()
    atomic_spec.add_atoms({"OK", "KO"})

    model = new_model()
    add_to_model(model, "OK", m1)
    assert(atomic_spec.apply(model) == {True  : {'OK' : {m1}, 'KO' : None},
                                        False : {'OK' : None, 'KO' : set([])}})

    add_to_model(model, "KO", m2)
    assert(atomic_spec.apply(model) == {True  : {'OK' : {m1}, 'KO' : {m2}},
                                        False : {'KO' : None, 'OK' : None}})
