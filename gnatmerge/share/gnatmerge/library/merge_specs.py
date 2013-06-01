"""Parser for merge specifications

A merge specification describes how heterogeneous results can be merged
in a higher-level entity.

This module provides three kinds of entities:
* a parser of merge specs (MergeSpec);
* a hierarchy of semantics for merge expressions (children of MergeSem);
* an abstract factory that bridges the gap between these two parts
(children of MergeSemFactory).

You may find a few examples in the body of function unit_testing.
"""

import shlex
from debug import log_method, log_function
from utils import attr_str, full_str, final_singleton
from elements import elements_union

class ParseError(Exception):
    """Exception raised when an invalid merge spec is given to parse
    """

    @log_method
    def __init__(self, text):
        """Constructor

        PARAMETERS
          text : message describing the error
        """
        self.text = text

    def __str__(self):
        """x.__str__() <==> str(x)"""
        return "merge spec error: %s" % self.text

class MergeSem:
    """Semantic helper for spec merges

    Children of this class provide various methods to compare models
    (e.g. sets of atoms that are true for the FreeSet case) verify a
    spec.

    REMARKS
      This is meant to be an abstract class; do not instanciate it.
      Make sure that children implement the abstract methods.
    """

    @log_method
    def apply(self, model):
        """Model morphism

        From the model in parameter, build and return a new model that
        represents only the truth value of the spec.

        For example, suppose that the models that we consider are such that
        they associate atoms with counterexamples:

            model = {KO : None, OK : overflow check not proved}

        ...and that we consider the spec named ALL_OK, with the expression

            ALL_PROVED = some OK and no KO

        ...then this method will return a model that associate the name of
        the spec (ALL_PROVED):

            result = {ALL_PROVED : overflow check not proved}

        REMARKS
          This method is abstract and should be implemented by children
          of this class.
        """
        assert(False)

class FreeSetMergeUnary(MergeSem):
    """Free set semantic helper for unary operators in spec merges

    This represents semantic helpers for atom (e.g. 'PROVED') that are
    qualified by an unary operator (e.g. 'some').

    ATTRIBUTES
      name: name attached to the spec merges (can be None)
      atom: atom that it qualifies. e.g. OK in 'some OK'.

    REMARKS
      This is meant to be an abstract class; do not instanciate it.
      Make sure that children implement the abstract methods.
    """
    @log_method
    def __init__(self, atom, name=None):
        """Incomplete constructor, to be called from the child's constructor
        """
        self.name = None
        self.atom = atom

    @log_method
    def apply(self, model):
        """Implementation of MergeSem.apply for unary operators"""
        if self.check(model):
            return {self.name}
        else:
            return set([])

class FreeSetMergeSome(FreeSetMergeUnary):
    """Free set semantic helper for some-quantified atoms in spec merges
    """

    @log_method
    def check(self, model):
        """Return True if the expression is True for model"""
        return self.atom in model

    def __str__(self):
        """x.__str__() <==> str(x)"""
        name = attr_str(self, 'name')
        expression = attr_str(self, 'atom', "some %s")
        return "<FreeSetMergeSome> (%s%s)" % (name, expression)

class FreeSetMergeNo(FreeSetMergeUnary):
    """Free set semantic helper for no-quantified atoms in spec merges
    """

    @log_method
    def check(self, model):
        """Return True if the expression is True for model"""
        return self.atom not in model

    def __str__(self):
        """x.__str__() <==> str(x)"""
        name = attr_str(self, 'name')
        expression = attr_str(self, 'atom', "no %s")
        return "<FreeSetMergeNo> (%s%s)" % (name, expression)

class FreeSetMergeBinary(MergeSem):
    """Free set semantic helper for binary operators in spec merges

    This represents semantic helpers (e.g. ['PROVED', 'TESTED'])
    binded with a given binary operators (e.g. 'and').

    ATTRIBUTES
      name: name attached to the spec merges (can be None)
      operands: operands of the considered binary operator

    ATTRIBUTES TO BE IMPLEMENTED IN CHILDREN
      operator : function that takes two booleans and returns a boolean,
                 to be used to merge two results of check() for two operands.
                 (e.g. lambda l, r: (l and r) to represent a 'and').
      identity : Boolean such that operator(identity, x) = x

    REMARKS
      This is meant to be an abstract class; do not instanciate it.
      Make sure that children implement the abstract methods.
    """

    @log_method
    def __init__(self, operands, name=None):
        """Incomplete constructor to be called in children"""
        self.name = None
        self.operands = operands

    @log_method
    def check(self, model):
        """Return True if the expression is True for model"""
        result = self.identity
        for operand in self.operands:
            result = self.operator(result, operand.check(model))
        return result

    @log_method
    def apply(self, model):
        """Implementation of MergeSem.apply for binary ops"""
        if self.check(model):
            return {self.name}
        else:
            return set([])

class FreeSetMergeAnd(FreeSetMergeBinary):
    """Free set semantic helper for and-binded helpers

    This provides the obvious corresponding semantics for and:
    i.e. self.check(model) returns True if all operand.check(model) return
    True, and otherwise returns False.
    """

    @log_method
    def __init__(self, operands, name=None):
        """Constructor - See description of attributes in FreeSetMergeBinary"""
        FreeSetMergeBinary.__init__(self, operands, name)
        self.operator = lambda l, r: (l and r)
        self.identity = True

    def __str__(self):
        """x.__str__() <==> str(x)"""
        name = attr_str(self, 'name')

        if 'operands' in dir(self):
            expression = " and ".join([full_str(o) for o in self.operands])
        else:
            expression = ""

        return "<FreeSetMergeAnd> (%s%s)" % (name, expression)

class FreeSetMergeOr(FreeSetMergeBinary):
    """Free set semantic helper for or-binded helpers

    This provides the obvious corresponding semantics for or:
    i.e. self.check(model) returns False if all operand.check(model) return
    False, and otherwise returns True.
    """

    @log_method
    def __init__(self, operands, name=None):
        """Constructor - See description of attributes in MergeBinary"""
        FreeSetMergeBinary.__init__(self, operands, name)
        self.operator = lambda l, r: (l or r)
        self.identity = False

    def __str__(self):
        """x.__str__() <==> str(x)"""
        name = attr_str(self, 'name', '%s = ')

        if 'operands' in dir(self):
            expression = " or ".join([full_str(o) for o in self.operands])
        else:
            expression = ""

        return "<FreeSetMergeOr> (%s%s)" % (name, expression)

class MergeSemFactory:
    """Abstract factory for semantics of merge spec
    """

    @log_method
    def build_merge_some(self, atom, name=None):
        """Build a semantic helper for an expression of the form "some <atom>"

        RETURNS
          The result of the build

        REMARKS
          This method is abstract and should be implemented by children
          of this class.
        """
        assert(False)

    @log_method
    def build_merge_no(self, atom, name=None):
        """Build a semantic helper for an expression of the form "no <atom>"

        RETURNS
          The result of the build

        REMARKS
          This method is abstract and should be implemented by children
          of this class.
        """
        assert(False)

    @log_method
    def build_merge_and(self, operands, name=None):
        """Build a semantic helper for a list of and-binded operands

        RETURNS
          The result of the build

        REMARKS
          This method is abstract and should be implemented by children
          of this class.
        """
        assert(False)

    @log_method
    def build_merge_or(self, operands, name=None):
        """Build a semantic helper for a list of or-binded operands

        RETURNS
          The result of the build

        REMARKS
          This method is abstract and should be implemented by children
          of this class.
        """
        assert(False)

@final_singleton
class FreeSetMergeFactory(MergeSemFactory):
    """Factory for simple semantics of merge specs

    In the free set semantics, models are sets of atoms
    (e.g. {'PROVED', 'TESTED'}). This class allows to recursively build
    semantic helper from a spec expression.

    """

    @log_method
    def build_merge_some(self, atom, name=None):
        "Implementation of SemMergeFactory.build_merge_some for sets"
        return FreeSetMergeSome(atom, name)

    @log_method
    def build_merge_no(self, atom, name=None):
        "Implementation of SemMergeFactory.build_merge_no for sets"
        return FreeSetMergeNo(atom, name)

    @log_method
    def build_merge_and(self, operands, name=None):
        "Implementation of SemMergeFactory.build_merge_and for sets"
        return FreeSetMergeAnd(operands, name)

    @log_method
    def build_merge_or(self, operands, name=None):
        "Implementation of SemMergeFactory.build_merge_or for sets"
        return FreeSetMergeOr(operands, name)

terminals = {"(", ")", "and", "or", "no", "some"}

class MergeSpec:

    @log_method
    def __init__ (self, spec, sem_factory, name=None):
        """Build an internal representation of a merge spec

        A merge spec follows this syntax:

        <atom> ::= <some alphanumerical text>
        <unary> ::= <atom> | 'some' <atom> | 'no' <atom>
        <expr> ::= '(' <status> ')' | <unary>
        <and_expr> ::= <expr> ('and' <expr>)*
        <or_expr> ::= <and_expr> ('or' <and_expr>)*
        <status>  ::= <or_expr>

        PARAMETERS
          spec: a string representation of the spec, following the syntax
        """
        self.spec = spec
        self.sem_factory = sem_factory
        lexer = shlex.shlex(spec)
        e = lexer.get_token()
        tokens = []
        while e != '':
            tokens.append(e)
            e = lexer.get_token()
        self.tokens = tuple(tokens)
        self.sem, index = self.__parse_status(0)
        self.sem.name = name

    @log_method
    def __parse_status(self, index):
        """Internal function - parse <status>"""
        left, index = self.__parse_and(index)
        left = [left,]
        while self.__token_look(index) == 'or':
            index += 1
            right, index = self.__parse_and(index)
            left.append(right)
        if len(left) > 1:
            return self.sem_factory.build_merge_or(left), index
        else:
            return left.pop(), index

    @log_method
    def __parse_and(self, index):
        """Internal function - parse <and_expr>"""
        left, index = self.__parse_expr(index)
        left = [left,]
        while self.__token_look(index) == 'and':
            index += 1
            right, index = self.__parse_expr(index)
            left.append(right)
        if len(left) > 1:
            return self.sem_factory.build_merge_and(left), index
        else:
            return left.pop(), index

    @log_method
    def __parse_expr(self, index):
        """Internal function - parse <expr>"""
        token = self.__token_look(index)

        if token == '(':
            index += 1
            result, index = self.__parse_status(index)
            token = self.__token_look(index)
            if token != ')':
                raise ParseError("unmatched parenthesis in '%s'"
                                 % self.spec)
            else:
                index += 1

        elif token == 'some':
            index += 1
            token = self.__token_look(index)
            if not self.__is_atom(token):
                raise ParseError("'some' not followed by identifier in '%s'"
                                 % self.spec)
                result = None
            else:
                result = self.sem_factory.build_merge_some(token)
                index += 1

        elif self.__is_atom(token):
            result = self.sem_factory.build_merge_some(token)
            index += 1

        elif token == 'no':
            index += 1
            token = self.__token_look(index)
            if not self.__is_atom(token):
                raise ParseError("'no' not followed by identifier in '%s'"
                                 % self.spec)
                result = None
            else:
                result = self.sem_factory.build_merge_no(token)
                index += 1

        else:
            raise ParseError("unrecognized token in '%s': %s"
                             % (self.spec, token))

        return result, index

    @log_method
    def __is_atom(self, token):
        """Internal function - Return True if token is an atom"""
        return token not in terminals

    @log_method
    def __token_look(self, index):
        """Internal function

        Return token at index, or None if out of bounds"""
        if index < len(self.tokens):
            return self.tokens[index]
        else:
            return None

    @log_method
    def check(self, model):
        """Check model against expression - See MergeSem.check"""
        return self.sem.check(model)

    @log_method
    def proof(self, model, result):
        """Return a proof of result for model - See MergeSem.proof"""
        return self.sem.proof(model, result)

    @log_method
    def apply(self, model):
        """Model morphism - See MergeSem.apply
        """
        return self.sem.apply(model)

    def __str__(self):
        """x.__str__() <==> str(x)"""
        spec = attr_str(self, 'spec', ' %s')
        return "<mergeSpec>%s" % spec

@log_function
def unit_testing():
    """Unit tests for this module

    The body of this function also provides a few useful examples that
    shows how the functions defined in this module work.
    """
    # A simple case: merging fragments with two possible status (OK or KO);
    # and making sure that there are no KO in these fragments, and at least
    # one OK to detect the case where no fragment has been contributed.
    spec = MergeSpec("some OK and no KO", FreeSetMergeFactory(), name="ALL_OK")

    assert(spec.apply({'OK'}) == {"ALL_OK"})
    assert(spec.apply({'OK', 'KO'}) == set([]))
    assert(spec.apply({'KO'}) == set([]))
    assert(spec.apply(set([])) == set([]))

    # A typical example in the case when proof and tests are merged:
    # If a procedure is not proved, then it should be both validated
    # and covered for a given criterion.
    spec = MergeSpec("(VALIDATED and COVERED) or PROVED",
                     FreeSetMergeFactory(),
                     name="OK")
    assert(spec.apply({'VALIDATED', 'COVERED'}) == {"OK"})
    assert(spec.apply({'VALIDATED'}) == set([]))
    assert(spec.apply({'PROVED'}) == {"OK"})
