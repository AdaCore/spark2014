"""Merges from one status space to another

This module provide ways to map the power set of status space to an
other status space; e.g. the status space of VCs ("VC_PROVED",
"VC_NOT_PROVED") to the status space of an enclosing source entity
(e.g. "FULLY PROVED", "NOT PROVED", "PARTIALLY PROVED"). The map is
expressed using merge specifications (as defined in module merge_specs).

See unit_testing for a few use cases.
"""

from merge_specs import MergeSpec
from status import MergeStatusFactory
from elements import elements_union
from debug import log_method, log_function

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
    def check(self, model):
        """Check model against expressions

        Same as MergeSpec.check, but for several named expressions; return
        the set of names whose expressions are verified in model.
        """
        return {key for key in self.map if self.map[key].check(model)}

    @log_method
    def proof(self, model, result):
        """Check model against expressions

        Same as MergeSpec.proof, but for several named expressions; return
        a dictionnary whose keys are the name of the expression that evaluated
        to result, and whose values are the corresponding proofs.
        """
        return {key : elements_union(self.map[key].proof(model, result))
                for key in self.map if self.map[key].check(model) == result}

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

    model = {}
    assert(spec_map.check(model) == {"NO VCS", "OK SO FAR"})
    assert(spec_map.proof(model, True)  == {"NO VCS"           : set([]),
                                            "OK SO FAR"        : set([])})
    assert(spec_map.proof(model, False) == {"PROVED"           : set([]),
                                            "PARTIALLY PROVED" : set([]),
                                            "STRICTLY PARTIAL" : set([]),
                                            "NOT PROVED"       : set([])})

    model["OK"] = {m1}
    assert(spec_map.check(model) == {"PROVED", "PARTIALLY PROVED",
                                     "OK SO FAR"})
    assert(spec_map.proof(model, True)  == {"PROVED"           : {m1},
                                            "OK SO FAR"        : set([]),
                                            "PARTIALLY PROVED" : {m1}})
    assert(spec_map.proof(model, False) == {"NO VCS"           : {m1},
                                            "STRICTLY PARTIAL" : set([]),
                                            "NOT PROVED"       : {m1}})

    model["KO"] = {m2}
    assert(spec_map.check(model) == {"PARTIALLY PROVED", "STRICTLY PARTIAL"})
    assert(spec_map.proof(model, True)  == {"PARTIALLY PROVED" : {m1},
                                            "STRICTLY PARTIAL" : {m1, m2}})
    assert(spec_map.proof(model, False) == {"NO VCS"           : {m1, m2},
                                            "PROVED"           : {m2},
                                            "OK SO FAR"        : {m2},
                                            "NOT PROVED"       : {m1}})

    model = {"KO" : {m2, m4}}
    assert(spec_map.check(model) == {"NOT PROVED"})
    assert(spec_map.proof(model, True)  == {"NOT PROVED"       : {m2, m4}})
    assert(spec_map.proof(model, False) == {"NO VCS"           : {m2, m4},
                                            "PROVED"           : {m2, m4},
                                            "OK SO FAR"        : {m2, m4},
                                            "PARTIALLY PROVED" : set([]),
                                            "STRICTLY PARTIAL" : set([])})
