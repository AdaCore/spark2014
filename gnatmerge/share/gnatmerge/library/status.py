"""Status model as merge semantics

This provide a semantics for merge specs that is based on status models.

Roughly speaking, a status model contain:
* states (e.g. "NOT_PROVED", "TESTS_FAILED");
* for each status, a proof or a counterexample for this status. i.e.
  a list of messages from a tool explaining why this status is
  (or is not) reached.

This is encoded as follow. First, a status model is a dictionary with
two keys, True and False; on the True side, proofs; on the False side,
counterexamples.

 <status_model> ::=  {True : <proofs>, False : <counterexamples>}

Proofs and counterexamples are both dictionnaries that associates
states with the corresponding justification of the current status
(e.g. error messages from a tool); None if this status is false:

 <proofs>          ::= {<status> : (<justification>|None) ...}
 <counterexamples> ::= {<status> : (<justification>|None) ...}

Two invariants:
 * <proofs> and <counterexamples> have the same keys/status;
 * A key points to None in exactly one of the two (meaning that
   a status has either a counterexample or a proof).
"""

from merge_specs import MergeSemFactory, MergeSem
from elements import dicts_union, elements_union_gen, elements_union_0, elements_union_1
from utils import attr_str, full_str, final_singleton
from debug import log_method, log_function

class StatusSome(MergeSem):
    """Status semantics for some-quantified atoms in spec merges

    This represents semantic for atom (e.g. 'PROVED') that are
    qualified by 'some'.

    ATTRIBUTES
      name: name attached to the spec merges (can be None)
      atom: atom that it qualifies. e.g. OK in 'some OK'.
    """

    @log_method
    def __init__(self, atom, name=None):
        """Constructor - See description of attributes in StatusSome"""
        self.atom = atom
        self.name = name

    @log_method
    def check(self, model):
        """Implementation of MergeSem.check for some-quantified atoms"""
        return self.atom in model

    @log_method
    def proof(self, model, result):
        """Implementation of MergeSem.proof for some-quantified atoms"""
        if result and self.atom in model:
            return {self.atom : model[self.atom]}
        else:
            return {}

    @log_method
    def apply(self, model):
        if self.atom not in model[True]:
            return {True  : {self.name : None},
                    False : {self.name : set([])}}
        else:
            return {True  : {self.name : model[True].get(self.atom)},
                    False : {self.name : model[False].get(self.atom)}}

    def __str__(self):
        """x.__str__() <==> str(x)"""
        name = attr_str(self, 'name', '%s ')
        expression = attr_str(self, 'atom', "some %s")
        return "<StatusSome> (%s%s)" % (name, expression)

class StatusNo(MergeSem):
    """Status semantics for no-quantified atoms in spec merges

    This represents semantic for atom (e.g. 'PROVED') that are
    qualified by 'no'.

    ATTRIBUTES
      name: name attached to the spec merges (can be None)
      atom: atom that it qualifies. e.g. OK in 'no OK'.
    """

    @log_method
    def __init__(self, atom, name=None):
        """Constructor - See description of attributes in StatusNo"""
        self.atom = atom
        self.name = name

    @log_method
    def check(self, model):
        """Implementation of MergeSem.check for no-quantified atoms"""
        return not self.atom in model

    @log_method
    def proof(self, model, result):
        """Implementation of MergeSem.proof for no-quantified atoms"""
        if not result and self.atom in model:
            return {self.atom : model[self.atom]}
        else:
            return {}

    @log_method
    def apply(self, model):
        if self.atom not in model[True]:
            return {True  : {self.name : set([])},
                    False : {self.name : None}}
        else:
            return {True  : {self.name : model[False].get(self.atom)},
                    False : {self.name : model[True].get(self.atom)}}

    def __str__(self):
        """x.__str__() <==> str(x)"""
        name = attr_str(self, 'name', '%s ')
        expression = attr_str(self, 'atom', "no %s")
        return "<StatusNo> (%s%s)" % (name, expression)

class StatusAnd(MergeSem):
    """Status semantics for and-binded operands in spec merges

    This represents semantic for operands that are binded
    by 'and'.

    ATTRIBUTES
      name:     name attached to the spec merges (can be None)
      operands: list of statuses to bind
    """

    @log_method
    def __init__(self, operands, name=None):
        """Constructor - See description of attributes in StatusAnd"""
        self.operands = operands
        self.name = name

    @log_method
    def check(self, model):
        """Implementation of MergeSem.check for and-binded operands"""
        for operand in self.operands:
            if not operand.check(model):
                return False
        return True

    @log_method
    def proof(self, model, result):
        """Implementation of MergeSem.proof for and-binded operands"""
        return dicts_union([operand.proof(model, result)
                            for operand in self.operands
                            if operand.check(model) == result])

    @log_method
    def apply(self, model):
        down = [op.apply(model) for op in self.operands]
        pros = [d[True] for d in down]
        cons = [d[False] for d in down]
        return {True  : {self.name :
                         elements_union_0([e for e
                                           in elements_union_gen(pros)])},
                False : {self.name :
                         elements_union_1([e for e
                                           in elements_union_gen(cons)])}}

    def __str__(self):
        """x.__str__() <==> str(x)"""
        name = attr_str(self, 'name', '%s ')

        if 'operands' in dir(self):
            expression = " and ".join([full_str(o) for o in self.operands])
        else:
            expression = ""

        return "<StatusAnd> (%s%s)" % (name, expression)

class StatusOr(MergeSem):
    """Status semantics for and-binded operands in spec merges

    This represents semantic for operands that are binded
    by 'or'.

    ATTRIBUTES
      name:     name attached to the spec merges (can be None)
      operands: list of statuses to bind
    """

    @log_method
    def __init__(self, operands, name=None):
        """Constructor - See description of attributes in StatusOr"""
        self.operands = operands
        self.name = name

    @log_method
    def check(self, model):
        """Implementation of MergeSem.check for or-binded operands"""
        for operand in self.operands:
            if operand.check(model):
                return True
        return False

    @log_method
    def proof(self, model, result):
        """Implementation of MergeSem.proof for or-binded operands"""
        return dicts_union([operand.proof(model, result)
                            for operand in self.operands
                            if operand.check(model) == result])

    @log_method
    def apply(self, model):
        down = [op.apply(model) for op in self.operands]
        pros = [d[True] for d in down]
        cons = [d[False] for d in down]
        return {True  : {self.name :
                         elements_union_1([e for e
                                           in elements_union_gen(pros)])},
                False : {self.name :
                         elements_union_0([e for e
                                           in elements_union_gen(cons)])}}

    def __str__(self):
        """x.__str__() <==> str(x)"""
        name = attr_str(self, 'name', '%s ')

        if 'operands' in dir(self):
            expression = " or ".join([full_str(o) for o in self.operands])
        else:
            expression = ""

        return "<StatusOr> (%s%s)" % (name, expression)

@final_singleton
class MergeStatusFactory(MergeSemFactory):
    """Factory for simple status of merge specs

    In the status semantics, models are dictionaries where status labels
    indexes sets of elements that verify the corresponding status
    (e.g. {'PROVED' : {m1, m2}, 'TESTED' : {m3}}).
    This class allows to recursively build semantic helpers from a spec
    expression.
    """

    @log_method
    def __init__(self):
        """Constructor"""
        pass

    @log_method
    def build_merge_some(self, atom, name=None):
        "Implementation of SemMergeFactory.build_merge_some for dicts"
        return StatusSome(atom, name)

    @log_method
    def build_merge_no(self, atom, name=None):
        "Implementation of SemMergeFactory.build_merge_no for dicts"
        return StatusNo(atom, name)

    @log_method
    def build_merge_and(self, operands, name=None):
        "Implementation of SemMergeFactory.build_merge_and for dicts"
        return StatusAnd(operands, name)

    @log_method
    def build_merge_or(self, operands, name=None):
        "Implementation of SemMergeFactory.build_merge_or for dicts"
        return StatusOr(operands, name)

@log_function
def unit_testing():
    """Unit tests for this module

    The body of this function also provides a few useful examples that
    shows how the functions defined in this module work.
    """
    from merge_specs import MergeSpec
    from messages import Message

    spec = MergeSpec("some OK and no KO", MergeStatusFactory(), "ALL_OK")
    m1 = Message(name ="VC1", status="OK", sloc="p.adb:1:1",
                 message="overflow check proved")
    m2 = Message(name ="VC2", status="KO", sloc="p.adb:2:2",
                 message="overflow check not proved")
    m3 = Message(name ="VC3", status="OK", sloc="p.adb:3:3",
                 message="assertion proved")
    m4 = Message(name ="VC4", status="KO", sloc="p.adb:4:4",
                 message="assertion not proved")

    model = {}
    assert(not spec.check(model))
    assert(spec.proof(model, True)  == {})
    assert(spec.proof(model, False) == {})

    model["OK"] = {m1}
    assert(spec.check(model))
    assert(spec.proof(model, True)  == {"OK" : {m1}})
    assert(spec.proof(model, False) == {})

    model["KO"] = {m2}
    assert(not spec.check(model))
    assert(spec.proof(model, True)  == {"OK" : {m1}})
    assert(spec.proof(model, False) == {"KO" : {m2}})

    model["OK"].add(m3)
    assert(not spec.check(model))
    assert(spec.proof(model, True)  == {"OK" : {m1, m3}})
    assert(spec.proof(model, False) == {"KO" : {m2}})

    model["KO"].add(m4)
    assert(not spec.check(model))
    assert(spec.proof(model, True)  == {"OK" : {m1, m3}})
    assert(spec.proof(model, False) == {"KO" : {m2, m4}})

    def add_to_model(model, key, element):
        if key in model[True]:
            model[True][key].add(element)
        else:
            model[True][key] = {element}
            model[False][key] = None

    model = {True : {}, False : {}}
    assert(spec.apply(model) == {True  : {"ALL_OK" : None},
                                 False : {"ALL_OK" : set([])}})

    add_to_model(model, "OK", m1)
    assert(spec.apply(model) == {True  : {"ALL_OK" : {m1}},
                                 False : {"ALL_OK" : None}})

    add_to_model(model, "KO", m2)
    assert(spec.apply(model) == {True  : {"ALL_OK" : None},
                                 False : {"ALL_OK" : {m2}}})

    add_to_model(model, "OK", m3)
    assert(spec.apply(model) == {True  : {"ALL_OK" : None},
                                 False : {"ALL_OK" : {m2}}})

    add_to_model(model, "KO", m4)
    assert(spec.apply(model) == {True  : {"ALL_OK" : None},
                                 False : {"ALL_OK" : {m2, m4}}})

