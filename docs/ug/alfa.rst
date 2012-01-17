Definition of Alfa
==================

Rationale
---------

Alfa is a subset of Ada 2012 described in the Alfa Reference Manual. It is
intended to be the largest possible subset of Ada amenable to automatic
proving.

In the context of Ada 2012, aspects are natural means of expressing important
features such as subprogram contracts or test case definitions, so Alfa is
defined in terms of these Ada 2012 features. For legacy applications, GNATprove
and GNATtest also support other Ada versions (83, 95, 2005), where specific
GNAT pragmas can be used to replace the important features mentioned above.

Alfa is meant to facilitate the expression of functional properties on Ada
programs, so that these properties can be verified either by testing or by
formal proof or by a combination thereof. Compared to the existing SPARK
annotated subset of Ada, Alfa is less constraining, but it does not
allow specifying and verifying data-and-control coupling properties. In
the absence of functional property definitions, the parts of an Ada program
that are in the Alfa subset can still be proven free of run-time errors.

Alfa is supported in the tools GNATtest and GNATprove, aiming respectively at
unit testing and unit proof of Ada subprograms. Annotations that specify the
functional behavior of the program can be executed, or not, during a run of the
program, and a failure to match the expected behavior results then in an error
being reported at run time through the exception mechanism. The tool GNATtest
automates the generation of a test harness and the verification that a
user-provided test procedure implements a specified formal test-case. The same
annotations can be analyzed statically with GNATprove to show that the program
is free from run-time errors and that it follows its expected behavior. A
crucial feature of GNATprove is that it interprets annotations
exactly like they are interpreted at run time during tests. In particular,
their executable semantics includes the verification of run-time checks, which
can be verified statically with GNATprove.  GNATprove can perform additional
verifications on the specification of the expected behavior itself, and its
correspondence to the code.

Currently, Alfa is only concerned with sequential execution of subprograms. A
future version of Alfa could include support of tasking with restrictions
similar to the ones found in Ravenscar or RavenSPARK. The main features from
Ada absent from Alfa are: exceptions, pointers (access types) and controlled
types. Each of these features has the potential to make automatic
formal verification very difficult, hence their rejection. Note that, in many
cases, ad-hoc data structures based on pointers can be replaced by the use
of standard Ada containers (vectors, lists, sets, maps, etc.) Although the
implementation of standard containers is not in Alfa, we have defined a
slightly modified version of these targeted at formal verification. These formal
containers are implemented in the GNAT standard library. These alternative
containers are typical of the tradeoffs implicit in Alfa: favor automatic formal
verification as much as possible, at the cost of minor adaptations to the code.

Alfa is still evolving, so that features not yet supported could be so in the
future. However, the definition and evolution of Alfa should respect the
following principles:

1. Annotations are free of side effects

No writes to global variables are allowed in annotations (contracts,
assertions, etc.). The possibility of run-time errors in annotations should be
detected in formal proofs.

2. Code is unambiguous

No behavior should depend on compiler choices (parameter passing, order of
evaluation of expressions, etc.)

3. Global effects of subprograms are generated

No manual annotations are needed for variables read and written by subprograms,
contrary to SPARK, JML, ACSL, Spec#. This requires all subprograms called to be
implemented.

4. Subprograms in Alfa / not in Alfa can be mixed

Provable and unprovable code can be combined at a fine-grain level. Provable
code can call unprovable code, and vice-versa.

Combining Alfa and Full Ada Code
--------------------------------

A subprogram is either:

* not in Alfa, when its specification is not in Alfa;

* fully in Alfa, when its specification and implementation are in Alfa (in Alfa for short);

* partially in Alfa, when its specification is in Alfa and its implementation is not in Alfa.

For a subprogram specification to be in Alfa, all the types of its parameters
(and result for a function) must be in Alfa, and all expressions mentioned in
its contract must be in Alfa. For a subprogram implementation to be in Alfa,
its specification must be in Alfa, all local declarations must be in Alfa
(types, variables, subprograms, etc.), all expressions and statements mentioned
in its body must be in Alfa, and finally all calls in its body must be to
subprograms at least partially in Alfa.

A consequence of this definition is that a subprogram fully in Alfa can only
call subprograms that are themselves partially or fully in Alfa. A subprogram
partially or not in Alfa can call any kind of subprogram. Further restrictions
apply to calls in annotations.

Most formal verification activities performed with GNATprove address
subprograms that are fully in Alfa. Some activities, which apply to the
contract of the subprogram only, also address subprograms that are partially in
Alfa.

.. comment: don't we need something about "alfa friendlyness" here?

Automatic Detection of Subprograms in Alfa
------------------------------------------

GNATprove automatically detects which subprograms are fully in Alfa, and which
subprograms are either not in Alfa or only partially in Alfa. Thus, the user
does not have to annotate the code to provide this information. However, the
user can review the results of this automatic detection, and require that some
subprograms are fully in Alfa (leading to an error if not).

.. _summary file:

Summary File
^^^^^^^^^^^^

The information of which subprograms are fully in Alfa and which are not, as
well as whether the features used in subprograms are already implemented or not,
is stored in a file with extension .alfa for review by the user, and to produce
global :ref:`project statistics`.

GNATprove outputs which features not in Alfa are used (using parentheses):

* access: access types and dereferences;
* ambiguous expr: ambiguous expression;
* assembly language: assembly language;
* deallocation: unchecked deallocation;
* dynamic allocation: dynamic allocation;
* exception: raising and catching exceptions;
* goto: goto;
* indirect call: indirect call;
* tasking: tasking;
* unchecked conversion: unchecked conversion;
* impure function: functions which write to variables other than parameters;
* recursive call: forbidden types of recursive calls, e.g. in contracts;
* unsupported construct: any other unsupported construct.

GNATprove outputs which features in Alfa but not yet implemented are used
[using brackets]:

* aggregate: array or record aggregate;
* arithmetic operation: arithmetic operation;
* attribute: not yet implemented attribute;
* concatenation: array concatenation;
* conversion: type conversion;
* container: formal container;
* discriminant: discriminant record;
* dispatch: dispatching;
* expression with action: expression with action;
* float: float;
* generic: generic;
* multi dim array: multi-dimensional array of dimention > 2;
* pragma: not yet implemented pragma;
* representation clause: representation clause;
* slice: array slice;
* tagged type: tagged type;
* type invariant;
* type predicate;
* operation on arrays: rarely used operation on arrays, such as boolean operators;
* iterators: loops with iterators;
* class wide types: class wide types;
* interfaces: interfaces;
* not yet implemented: any other not yet implemented construct.

As an example, consider the following code:

.. code-block:: ada

    package P is
       X : access Boolean;
       procedure P0;
    end P;

    package body P is
       procedure Set is
       begin
	  X.all := True;
       end Set;

       procedure P0 is
	  Y : Boolean;

	  function Get return Boolean is
	  begin
	     return X.all;
	  end Get;

	  procedure P1 is
	  begin
	     if not Get then
		return;
	     end if;
	     Y := True;
	  end P1;
       begin
	  Set;
	  P1;
       end P0;
    end P;

On this code, GNATprove outputs the following information in file p.alfa::

    -+ p__set p.adb:2 (access)
    -+ p__p0__get p.adb:10 (access)
    ++ p__p0__p1 p.adb:15
    -+ p__p0 p.ads:3 (access)

The first character denotes whether the subprogram body is fully in Alfa (+),
not in Alfa (-) or not yet implemented in Alfa (*). The second character
follows the same categories for the subprogram spec. The name that follows is a
unique name for the subprogram. The location of the subprogram is given next
with its file and line. Subprograms not in Alfa may be followed by a set of
features used that make it not Alfa, given in parentheses. Subprograms not in
Alfa or not yet implemented in Alfa may be followed by a set of features not
yet implemented, given in brackets, whose implementation would make the
subprogram in Alfa.

In the example above, P.Set (unique name: p__set) and P.P0.Get (unique name:
p__p0__get) are both partially in Alfa because their body both contain pointer
dereferences. P.P0.P1 (unique name: p__p0__p1) is fully in Alfa. Since P.Set is
partially in Alfa and defined as a local subprogram of P.P0, P.P0 is partially
in Alfa.

The purpose of the additional information on features not yet implemented is to
allow users to experiment and see which features are more beneficial in their
context, in order to prioritize efficiently their implementation.

User-specified Compliance
^^^^^^^^^^^^^^^^^^^^^^^^^

The user may require that the project only contains code in Alfa, by using
option ``--mode=force``. Any violation of Alfa is then reported as an error,
and any construct in Alfa not yet implemented is reported as a warning.

For a finer-grain control, the user may require that some subprograms are in
Alfa by inserting a specific pragma ``Annotate`` in the body of the
subprogram. He may also insert this pragma inside or before a package
declaration (spec or body) to require that all subprogram declarations in this
package are in Alfa.

On the following example:

.. code-block:: ada

    package P is
       pragma Annotate (gnatprove, Force);
       X : access Boolean;
       procedure P0;
    end P;

    package body P is
       procedure Set is
       begin
	  X.all := True;
       end Set;

       procedure P0 is
	  Y : Boolean;

	  function Get return Boolean is
	     pragma Annotate (gnatprove, Ignore);
	  begin
	     return X.all;
	  end Get;

	  procedure P1 is
	  begin
	     if not Get then
		return;
	     end if;
	     Y := True;
	  end P1;
       begin
	  Set;
	  P1;
       end P0;
    end P;

GNATprove outputs the following errors::

    p.adb:4:07: explicit dereference is not in Alfa
    p.ads:3:08: access type is not in Alfa

The error messages distinguish constructs not in Alfa (like a pointer
dereference) from constructs not yet implemented. Notice that no error is given
for the dereference in P.P0.Get, as another pragma Annotate in that subprogram
specifies that formal proof should not be done on this subprogram.

.. _project statistics:

Project Statistics
------------------

Based on the generated :ref:`summary file` for each source unit, GNATprove
generates global project statistics in file ``gnatprove.out``. The statistics
describe:

* what percentage and number of subprograms are in Alfa
* what percentage and number of Alfa subprograms are not yet supported
* what are the main reasons for subprograms not to be in Alfa
* what are the main reasons for subprograms not to be yet supported in Alfa
* units with the largest number of subprograms in Alfa
* units with the largest number of subprograms not in Alfa

A Non-ambiguous Subset of Ada
-----------------------------

The behaviour of a program in Alfa should be unique, both in order to
facilitate formal verification of properties over these programs, and to get
the additional guarantee that a formally verified Alfa program always behaves
the same.

Sources of ambiguity in sequential Ada programs are:

* order of evaluation of sub-expressions, which may interact with writes to
  globals through calls;
* evaluation strategy for arithmetic expressions, which may result in an
  overflow check passing or failing;
* bounds of base scalar types;
* compiler permissions, such as the permission for the compiler to compute the
  right result of an arithmetic expression even if a naive computation would
  raise an exception due to overflow.

In Alfa, none of these sources of ambiguity is possible.

No Writes to Globals in Functions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In Ada, a sub-expression can write to a global variable through a call. As the
order of evaluation of sub-expressions in an expression (for example, operands
of an arithmetic operation or arguments of a call) is not specified in Ada, the
time of this write may have an influence on the value of the expression. In
Alfa, functions cannot write to globals, which removes this source of
ambiguity.

Parenthesized Arithmetic Operations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In Ada, non-parenthesized arithmetic operations can be re-ordered by the
compiler, which may result in a failing computation (due to overflow checking)
becoming a successful one, and vice-versa. In Alfa, all such operations should
be parenthesized. (SPARK issues a warning on such cases.)

More specifically:

* any operand of a binary adding operation (+,-) that is itself a binary adding
  operation must be parenthesized;
* any operand of a binary multiplying operation (\*,/,mod,rem) that is itself a
  binary multiplying operation must be parenthesized.

Compiler Permissions
^^^^^^^^^^^^^^^^^^^^

Ada standard defines various ways in which a compiler is allowed to compute a
correct result for a computation instead of raising a run-time error. In Alfa,
we adopt by default the choices made by GNAT on the platform, except when 
option ``--pedantic`` is used, in which case we reject all such permissions 
and interpret all computations with the strictest meaning.

For example, the bounds of base types for user-defined types, which define 
which computations overflow, may vary depending on the compiler and host/target
architectures. With option ``--pedantic``, all bounds should be set to their 
minimum range
guaranteed by the Ada standard (worst case). For example, the following type
should have a base type ranging from -10 to 10 (standard requires a symmetric
range with a possible extra negative value)::

    type T is 1 .. 10;

This other type should have a base type ranging from -10 to 9::

    type T is -10 .. 1;

The bounds of standard scalar types are still defined by the GNAT compiler 
for every host/target architecture, even with option ``--pedantic``.

Pure Contract Specifications
----------------------------

Contract specifications and other assertions should have a pure logical meaning
and no visible effect on the computation, aside from possibly raising an
exception at run time when ill-defined (run-time error) or invalid (assertion
violation). This is guaranteed in Alfa by the restriction that functions should
not perform writes to global variables since a function call is the only
possible way of generating side effects within an expression.

Current Definition of Alfa
--------------------------

As indicated before, tasking is excluded from Alfa, as well as exceptions,
pointers (access types), controlled types and interfaces. Features of Ada for
object-oriented programming and generic programming are included in Alfa:
tagged types, dispatching, generics. Restrictions in Alfa do
not target increase in readability, so use-clause, overloading and renamings
are allowed for example. Also restrictions in Alfa do not
constrain control flow, so arbitrary exits from loops and returns in
subprograms are allowed. Note that, if desired, these restrictions can be
detected with a coding style checker like GNATcheck. The following sections
go into more details about what is or not in Alfa.

Function Calls in Annotations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The contracts of functions called in annotations are essential for automatic
proofs. Currently, the knowledge that a function call in an annotation respects
its postcondition (when called in a context where the precondition is
satisfied) is only available for expression functions. The syntax of expression
functions, introduced in Ada 2012, allows defining functions whose
implementation simply returns an expression, such as ``Even``, ``Odd`` and
``Is_Prime`` below.

.. code-block:: ada

    function Even (X : Integer) return Boolean is (X mod 2 = 0);

    function Odd (X : Integer) return Boolean is (not Even (X));

    function Is_Prime (X : Integer) with
      Pre => Is_Odd (X);

Calls to Standard Library Functions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The standard library for the selected target is pre-analyzed, so that user code
can freely call standard library subprograms.

Loop Invariants
^^^^^^^^^^^^^^^

In order for GNATprove to prove formally the properties of interest on
subprograms with loops, the user should annotate these loops with loop
invariants. A loop invariant gives information on the state at entry to the
loop at each iteration. Loop invariants in Alfa consist in the conjunction of
all assertions that appear at the beginning of the loop body. Loop invariants
may have to be precise enough to prove the property of interest. For example,
in order to prove the postcondition of function ``Contains`` below, one has to
write a precise loop invariant such as the one given below:

.. code-block:: ada

  function Contains (Table : IntArray; Value : Integer) return Boolean with
    Post => (if Contains'Result then
               (for some J in Table'Range => Table (J) = Value)
	     else
               (for all J in Table'Range => Table (J) /= Value));

  function Contains (Table : IntArray; Value : Integer) return Boolean is
  begin
     for Index in Table'Range loop
        pragma Assert (for all J in Table'First .. Index - 1 =>
                         Table (J) /= Value);

        if Table(Index) = Value then
           return True;
        end if;
     end loop;

     return False;
  end Contains;

When the loop involves modifying a variable, it may be necessary to refer to
the value of the variable at loop entry. This can be done using the GNAT
attribute ``'Loop_Entry``. For example, in order to prove the postcondition of
function ``Move`` below, one has to write a loop invariant referring to
``Src'Loop_Entry`` such as the one given below:

.. code-block:: ada

  procedure Move (Dest, Src : out IntArray) with
    Post => (for all J in Dest'Range => Dest (J) = Src'Old (J));

  procedure Move (Dest, Src : out IntArray) is
  begin
     for Index in Dest'Range loop
        pragma Assert ((for all J in Dest'First .. Index - 1 =>
                         Dest (J) = Src'Loop_Entry (J)) and
		       (for all J in Index .. Dest'Last =>
                         Src (J) = Src'Loop_Entry (J)));

        Dest (Index) := Src (Index);
        Src (Index) := 0;
     end loop;
  end Move;

Note that GNATprove does not yet support the use of attribute ``'Loop_Entry``,
which can be replaced sometimes by the use of attribute ``'Old`` referring to
the value of a variable at subprogram entry. Ultimately, uses of ``'Old``
outside of postconditions will be deprecated, once attribute ``'Loop_Entry`` is
supported.

Quantified Expressions
----------------------

Ada 2012 quantified expressions are a special case with respect to run-time
errors: the enclosed expression must be run-time error free over the *entire
range* of the quantification, not only at points that would actually be
reached at execution. As an example, consider the following expression:

.. code-block:: ada

    (for all I in 1 .. 10 => 1 / (I - 3) > 0)

This quantified expression will never raise a run-time error, because the
test is already false for the first value of the range, ``I = 1``, and the
execution will stop, with the result value ``False``. However, GNATprove
requires the expression to be run-time error free over the entire range,
including ``I = 3``, so there will be an unproved VC for this case.

Features Not Yet Implemented
----------------------------

The major features not yet implemented are:

* OO programming: tagged types, dispatching
* generics
* formal containers
* invariants on types (invariants and predicates)

Other important features not yet implemented are:

* discriminant / variant records
* array slices
* declare block statements
* elaboration code
* attribute ``'Loop_Entry``
