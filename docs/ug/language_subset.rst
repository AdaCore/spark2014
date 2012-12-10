Definition of |SPARK|
=====================

Rationale
---------

|SPARK| is a subset of Ada 2012 described in the |SPARK| Reference Manual. It is
intended to be the largest possible subset of Ada amenable to automatic
proving.

In the context of Ada 2012, aspects are natural means of expressing important
features such as subprogram contracts or test case definitions, so |SPARK| is
defined in terms of these Ada 2012 features. For legacy applications, |GNATprove|
and GNATtest also support other Ada versions (83, 95, 2005), where specific
GNAT pragmas can be used to replace the important features mentioned above.

|SPARK| is meant to facilitate the expression of functional properties on Ada
programs, so that these properties can be verified either by testing or by
formal proof or by a combination thereof. Compared to the existing SPARK
annotated subset of Ada, |SPARK| is less constraining, but it does not
allow specifying and verifying data-and-control coupling properties. In
the absence of functional property definitions, the parts of an Ada program
that are in the |SPARK| subset can still be proven free of run-time errors.

|SPARK| is supported in the GNAT compiler, as well as tools GNATtest and
|GNATprove|, aiming respectively at unit testing and unit proof of Ada
subprograms.  Annotations that specify the functional behavior of the program
can be executed, or not, during a run of the program, and a failure to match
the expected behavior results then in an error being reported at run time
through the exception mechanism. The tool GNATtest automates the generation of
a test harness and the verification that a user-provided test procedure
implements a specified formal test-case. The same annotations can be analyzed
statically with |GNATprove| to show that the program is free from run-time errors
and that it follows its expected behavior. A crucial feature of |GNATprove| is
that it interprets annotations exactly like they are interpreted at run time
during tests. In particular, their executable semantics includes the
verification of run-time checks, which can be verified statically with
|GNATprove|.  |GNATprove| can perform additional verifications on the specification
of the expected behavior itself, and its correspondence to the code.

Currently, |SPARK| is only concerned with sequential execution of subprograms. A
future version of |SPARK| could include support of tasking with restrictions
similar to the ones found in Ravenscar or RavenSPARK. The main features from
Ada absent from |SPARK| are: exceptions, pointers (access types) and controlled
types. Each of these features has the potential to make automatic
formal verification very difficult, hence their rejection. Note that, in many
cases, ad-hoc data structures based on pointers can be replaced by the use
of standard Ada containers (vectors, lists, sets, maps, etc.) Although the
implementation of standard containers is not in |SPARK|, we have defined a
slightly modified version of these targeted at formal verification. These formal
containers are implemented in the GNAT standard library. These alternative
containers are typical of the tradeoffs implicit in |SPARK|: favor automatic formal
verification as much as possible, at the cost of minor adaptations to the code.

|SPARK| is still evolving, so that features not yet supported could be so in the
future. However, the definition and evolution of |SPARK| should respect the
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

4. Subprograms in |SPARK| / not in |SPARK| can be mixed

Provable and unprovable code can be combined at a fine-grain level. Provable
code can call unprovable code, and vice-versa.

Features of Ada for object-oriented programming and generic programming are
included in |SPARK|: tagged types, dispatching, generics. Restrictions in |SPARK| do
not target increase in readability, so use-clause, overloading and renamings
are allowed for example. Also restrictions in |SPARK| do not constrain control
flow, so arbitrary exits from loops and returns in subprograms are
allowed. Note that, if desired, these restrictions can be detected with a
coding style checker like GNATcheck.

Combining |SPARK| and Full Ada Code
-----------------------------------

A subprogram is either:

* not in |SPARK|, when its specification is not in |SPARK|;

* fully in |SPARK|, when its specification and implementation are in |SPARK| (in |SPARK| for short);

* partially in |SPARK|, when its specification is in |SPARK| and its implementation is not in |SPARK|.

For a subprogram specification to be in |SPARK|, all the types of its parameters
(and result for a function) must be in |SPARK|, and all expressions mentioned in
its contract must be in |SPARK|. For a subprogram implementation to be in |SPARK|,
its specification must be in |SPARK|, all local declarations must be in |SPARK|
(types, variables, subprograms, etc.), all expressions and statements mentioned
in its body must be in |SPARK|, and finally all calls in its body must be to
subprograms at least partially in |SPARK|.

A consequence of this definition is that a subprogram fully in |SPARK| can only
call subprograms that are themselves partially or fully in |SPARK|. A subprogram
partially or not in |SPARK| can call any kind of subprogram.

Most formal verification activities performed with |GNATprove| address
subprograms that are fully in |SPARK|. Some activities, which apply to the
contract of the subprogram only, also address subprograms that are partially in
|SPARK|.

.. comment: don't we need something about "alfa friendlyness" here?

Automatic Detection of Subprograms in |SPARK|
---------------------------------------------

|GNATprove| automatically detects which subprograms are fully in |SPARK|, and which
subprograms are either not in |SPARK| or only partially in |SPARK|. Thus, the user
does not have to annotate the code to provide this information. However, the
user can review the results of this automatic detection, and require that some
subprograms are fully in |SPARK| (leading to an error if not).

.. _summary file:

Summary File
^^^^^^^^^^^^

The information of which subprograms are fully in |SPARK| and which are not, as
well as whether the features used in subprograms are already implemented or not,
is stored in a file with extension .alfa for review by the user, and to produce
global :ref:`project statistics`.

|GNATprove| outputs which features not in |SPARK| are used (using parentheses):

* access: access types and dereferences;
* assembly language: assembly language;
* deallocation: unchecked deallocation;
* dynamic allocation: dynamic allocation;
* exception: raising and catching exceptions;
* forward reference: forward reference to an entity;
* goto: goto;
* indirect call: indirect call;
* tasking: tasking;
* unchecked conversion: unchecked conversion;
* impure function: functions which write to variables other than parameters;
* recursive call: forbidden types of recursive calls, e.g. in contracts;
* uninitialized logic expr: expression which should be fully initialized;
* unsupported construct: any other unsupported construct.

|GNATprove| outputs which features in |SPARK| but not yet implemented are used
[using brackets]:

* aggregate: aggregate extension;
* arithmetic operation: not yet implemented arithmetic operation;
* attribute: not yet implemented attribute;
* concatenation: array concatenation;
* container: formal container;
* dispatch: dispatching;
* expression with action: expression with action;
* multi dim array: multi-dimensional array of dimention > 4;
* pragma: not yet implemented pragma;
* representation clause: representation clause;
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
   :linenos:

    package P is
       X : access Boolean;
       procedure P0;
    end P;

.. code-block:: ada
   :linenos:

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

On this code, |GNATprove| outputs the following information in file p.alfa::

    -+ p__set p.adb:2 (access)
    -+ p__p0__get p.adb:10 (access)
    ++ p__p0__p1 p.adb:15
    -+ p__p0 p.ads:3 (access)

The first character denotes whether the subprogram body is fully in |SPARK| (+),
not in |SPARK| (-) or not yet implemented in |SPARK| (*). The second character
follows the same categories for the subprogram spec. The name that follows is a
unique name for the subprogram. The location of the subprogram is given next
with its file and line. Subprograms not in |SPARK| may be followed by a set of
features used that make it not |SPARK|, given in parentheses. Subprograms not in
|SPARK| or not yet implemented in |SPARK| may be followed by a set of features not
yet implemented, given in brackets, whose implementation would make the
subprogram in |SPARK|.

In the example above, P.Set (unique name: p__set) and P.P0.Get (unique name:
p__p0__get) are both partially in |SPARK| because their body both contain pointer
dereferences. P.P0.P1 (unique name: p__p0__p1) is fully in |SPARK|. Since P.Set is
partially in |SPARK| and defined as a local subprogram of P.P0, P.P0 is partially
in |SPARK|.

The purpose of the additional information on features not yet implemented is to
allow users to experiment and see which features are more beneficial in their
context, in order to prioritize efficiently their implementation.

User-specified Compliance
^^^^^^^^^^^^^^^^^^^^^^^^^

The user may require that the project only contains code in |SPARK|, by using
option ``--mode=force``. Any violation of |SPARK| is then reported as an error,
and any construct in |SPARK| not yet implemented is reported as a warning.

For a finer-grain control, the user may require that some subprograms are in
|SPARK| by inserting a specific pragma ``Annotate`` in the body of the
subprogram. He may also insert this pragma inside or before a package
declaration (spec or body) to require that all subprogram declarations in this
package are in |SPARK|.

On the following example:

.. code-block:: ada
   :linenos:

    package P is
       pragma Annotate (gnatprove, Force);
       X : access Boolean;
       procedure P0;
    end P;

.. code-block:: ada
   :linenos:

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

|GNATprove| outputs the following errors::

    p.adb:4:07: explicit dereference is not in |SPARK|
    p.ads:3:08: access type is not in |SPARK|

The error messages distinguish constructs not in |SPARK| (like a pointer
dereference) from constructs not yet implemented. Notice that no error is given
for the dereference in P.P0.Get, as another pragma Annotate in that subprogram
specifies that formal proof should not be done on this subprogram.

.. _project statistics:

Project Statistics
------------------

Based on the generated :ref:`summary file` for each source unit, |GNATprove|
generates global project statistics in file ``gnatprove.out``. The statistics
describe:

* what percentage and number of subprograms are in |SPARK|
* what percentage and number of |SPARK| subprograms are not yet supported
* what are the main reasons for subprograms not to be in |SPARK|
* what are the main reasons for subprograms not to be yet supported in |SPARK|
* units with the largest number of subprograms in |SPARK|
* units with the largest number of subprograms not in |SPARK|

A Non-ambiguous Subset of Ada
-----------------------------

The behaviour of a program in |SPARK| should be unique, both in order to
facilitate formal verification of properties over these programs, and to get
the additional guarantee that a formally verified |SPARK| program always behaves
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

In |SPARK|, none of these sources of ambiguity is possible.

No Writes to Globals in Functions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In Ada, a sub-expression can write to a global variable through a call. As the
order of evaluation of sub-expressions in an expression (for example, operands
of an arithmetic operation or arguments of a call) is not specified in Ada, the
time of this write may have an influence on the value of the expression. In
|SPARK|, functions cannot write to globals, which removes this source of
ambiguity.

Parenthesized Arithmetic Operations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In Ada, non-parenthesized arithmetic operations could be re-ordered by the
compiler, which may result in a failing computation (due to overflow checking)
becoming a successful one, and vice-versa. In |SPARK|, we adopt by default the
choice made by GNAT which is to evaluate all expressions left-to-right, except
when option ``--pedantic`` is used, in which case a warning is emitted for
every operation that could be re-ordered.

More specifically, a warning is emitted when option ``--pedantic`` is set on:

* any operand of a binary adding operation (+,-) that is itself a binary adding
  operation;
* any operand of a binary multiplying operation (\*,/,mod,rem) that is itself a
  binary multiplying operation.

Compiler Permissions
^^^^^^^^^^^^^^^^^^^^

Ada standard defines various ways in which a compiler is allowed to compute a
correct result for a computation instead of raising a run-time error. In |SPARK|,
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
violation). This is guaranteed in |SPARK| by the restriction that functions should
not perform writes to global variables since a function call is the only
possible way of generating side effects within an expression.

Features Not Yet Implemented
----------------------------

The major features not yet implemented are:

* OO programming: tagged types, dispatching
* formal containers
* invariants on types (invariants and predicates)

Other important features not yet implemented are:

* discriminant / variant records
* elaboration code
* attribute ``'Loop_Entry``
