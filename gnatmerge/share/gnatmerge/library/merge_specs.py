"""Parser for merge specifications

A merge specification describes how heterogeneous results can be merged
in a higher-level entity.

You may find a few examples in the body of function unit_testing.
"""

import shlex
from debug import decorator

class ParseError(Exception):
    """Exception raised when an invalid merge spec is given to parse
    """

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

    Children of this class provide various methods to compare
    models (sets of atoms that are meant to represent the actual state
    of entity, e.g. {'PROVED', 'TESTED'}) verify a spec.

    REMARKS
      This is meant to be an abstract class; do not instanciate it.
      Make sure that children implement the abstract methods.
    """

    def check(self, model):
        """Check a model against the spec

        REMARKS
          This method is abstract and should be implemented by children
          of this class.
        """
        assert(False)

    def deduce_all(self, model):
        """Return all atoms that can be deduced from the model using this spec

        REMARKS
          This method is abstract and should be implemented by children
          of this class.
        """
        assert(False)

class MergeUnary(MergeSem):
    """Semantic helper for unary operators in spec merges

    This represents semantic helpers for atom (e.g. 'PROVED') that are
    qualified by an unary operator (e.g. 'some').

    ATTRIBUTES
      name: name attached to the spec merges (can be None)
      atom: atom that it qualifies. e.g. OK in 'some OK'.

    REMARKS
      This is meant to be an abstract class; do not instanciate it.
      Make sure that children implement the abstract methods.
    """
    def __init__(self, atom, name=None):
        """Incomplete constructor, to be called from the child's constructor
        """
        self.name = None
        self.atom = atom

    def deduce_all(self, model):
        """Implementation of MergeSem.deduce_all for all unary operators"""
        check = self.check(model)
        deduction = ({self.name,} if (check and self.name is not None)
                     else set([]))
        return check, deduction

class MergeSome(MergeUnary):
    """Semantic helper for some-quantified atoms in spec merges
    """

    def check(self, model):
        """Implementation of MergeSem.check for some-quantified atoms"""
        return self.atom in model

    def __str__(self):
        """x.__str__() <==> str(x)"""
        if self.name is not None:
            name_prefix = "%s = " % self.name
        else:
            name_prefix = ""

        expression = "some %s" % self.atom
        return "<MergeSome> (%s%s)" % (name_prefix, expression)

class MergeNo(MergeUnary):
    """Semantic helper for no-quantified atoms in spec merges
    """

    def check(self, model):
        """Implementation of MergeSem.check for no-quantified atoms"""
        return self.atom not in model

    def __str__(self):
        """x.__str__() <==> str(x)"""
        if self.name is not None:
            name_prefix = "%s = " % self.name
        else:
            name_prefix = ""

        expression = "no %s" % self.atom
        return "<MergeNo> (%s%s)" % (name_prefix, expression)

class MergeBinary(MergeSem):
    """Semantic helper for binary operators in spec merges

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

    def __init__(self, operands, name=None):
        """Incomplete constructor to be called in children"""
        self.name = None
        self.operands = operands

    def check(self, model):
        """Implementation of MergeSem.check for binary-binded operands"""
        result = self.identity
        for operand in self.operands:
            result = self.operator(result, operand.check(model))
        return result

    def deduce_all(self, model):
        """Implementation of MergeSem.deduce_all for binary-binded operands"""
        le = self.identity
        lm = set([])
        for operand in self.operands:
            re, rm = operand.deduce_all(model)
            le = self.operator(le, re)
            lm = lm.union(rm)
        if self.name is not None and le:
            lm.add(self.name)
        return le, lm

class MergeAnd(MergeBinary):
    """Semantic helper for and-binded helpers

    This provides the obvious corresponding semantics for and:
    i.e. self.check(model) returns True if all operand.check(model) return
    True, and otherwise returns False.
    """

    def __init__(self, operands, name=None):
        """Constructor - See description of attributes in MergeBinary"""
        MergeBinary.__init__(self, operands, name)
        self.operator = lambda l, r: (l and r)
        self.identity = True

    def __str__(self):
        """x.__str__() <==> str(x)"""
        if self.name is not None:
            name_prefix = "%s = " % self.name
        else:
            name_prefix = ""

        expression = " and ".join([str(o) for o in self.operands])
        return "<MergeAnd> (%s%s)" % (name_prefix, expression)

class MergeOr(MergeBinary):
    """Semantic helper for or-binded helpers

    This provides the obvious corresponding semantics for or:
    i.e. self.check(model) returns False if all operand.check(model) return
    False, and otherwise returns True.
    """

    def __init__(self, operands, name=None):
        """Constructor - See description of attributes in MergeBinary"""
        MergeBinary.__init__(self, operands, name)
        self.operator = lambda l, r: (l or r)
        self.identity = False

    def __str__(self):
        """x.__str__() <==> str(x)"""
        if self.name is not None:
            name_prefix = "%s =" % self.name
        else:
            name_prefix = ""

        expression = " or ".join([str(o) for o in self.operands])
        return "<MergeOr> (%s %s)" % (name_prefix, expression)

terminals = {"(", ")", "and", "or", "no", "some"}

class MergeSpec:

    def __init__ (self, spec, name=None):
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
        lexer = shlex.shlex(spec)
        e = lexer.get_token()
        tokens = []
        while e != '':
            tokens.append(e)
            e = lexer.get_token()
        self.tokens = tuple(tokens)
        self.ast, index = self.__parse_status(0)
        self.ast.name = name

    def __parse_status(self, index):
        """Internal function - parse <status>"""
        left, index = self.__parse_and(index)
        left = [left,]
        while self.__token_look(index) == 'or':
            index += 1
            right, index = self.__parse_and(index)
            left.append(right)
        if len(left) > 1:
            return MergeOr(left), index
        else:
            return left.pop(), index

    def __parse_and(self, index):
        """Internal function - parse <and_expr>"""
        left, index = self.__parse_expr(index)
        left = [left,]
        while self.__token_look(index) == 'and':
            index += 1
            right, index = self.__parse_expr(index)
            left.append(right)
        if len(left) > 1:
            return MergeAnd(left), index
        else:
            return left.pop(), index

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
                result = MergeSome(token)
                index += 1

        elif self.__is_atom(token):
            result = MergeSome(token)
            index += 1

        elif token == 'no':
            index += 1
            token = self.__token_look(index)
            if not self.__is_atom(token):
                raise ParseError("'no' not followed by identifier in '%s'"
                                 % self.spec)
                result = None
            else:
                result = MergeNo(token)
                index += 1

        else:
            raise ParseError("unrecognized token in '%s': %s"
                             % (self.spec, token))

        return result, index

    def __is_atom(self, token):
        """Internal function - Return True if token is an atom"""
        return token not in terminals

    def __token_look(self, index):
        """Internal function

        Return token at index, or None if out of bounds"""
        if index < len(self.tokens):
            return self.tokens[index]
        else:
            return None

    def check(self, model):
        """Same as MergeSem.check"""
        return self.ast.check(model)

    def maximalize(self, model):
        """Append all possible deductions

        Get all possible deductions from specs and model, and
        return the original model enriched with these deductions.
        """
        check, deduction = self.ast.deduce_all(model)
        return model.union(deduction)

def unit_testing():
    """Unit tests for this module

    The body of this function also provides a few useful examples that
    shows how the functions defined in this module work.
    """
    # A simple case: merging fragments with two possible status (OK or KO);
    # and making sure that there are no KO in these fragments, and at least
    # one OK to detect the case where no fragment has been contributed.
    spec = MergeSpec("some OK and no KO")
    assert(spec.check({'OK'}))
    assert(not spec.check({'KO', 'OK'}))
    assert(not spec.check({'KO'}))
    assert(not spec.check(set([])))

    # A typical example in the case when proof and tests are merged:
    # If a procedure is not proved, then it should be both validated
    # and covered for a given criterion.
    spec = MergeSpec("(VALIDATED and COVERED) or PROVED", name="OK")
    assert(spec.check({'VALIDATED', 'COVERED'}))
    assert(not spec.check({'VALIDATED'}))
    assert(spec.check({'PROVED'}))
    assert(spec.maximalize({'PROVED'}) == {'PROVED', 'OK'})
