Definition of Alfa
==================

Rationale
---------

Alfa is a subset of Ada 2012, augmented with GNAT-specific extensions. The most
prominent features (contracts, test-cases) are also available in other Ada
modes (83, 95, 2005) through GNAT pragmas. Alfa is meant to facilitate the
expression of behavioral properties on Ada programs, so that these properties
can be verified either by testing or by formal proof or by a combination
thereof. Compared to the existing SPARK annotated subset of Ada, Alfa is much
less constraining, but it does not allow specifying and verifying
data-and-control coupling properties.

Alfa is supported in the tools GNATtest and GNATprove, aiming respectively at
unit testing and unit proof of Ada subprograms. Annotations that specify the
behavior of the program can be executed during a run of the program, either
during development or tests, and a failure to match the expected behavior
results then in an error being reported through the exception mechanism. The
tool GNATtest automates the generation of a test harness and the verification
that a user-provided test procedure implements a specified formal test-case.
The same annotations can be analyzed statically with GNATprove to show that the
program is free from run-time errors and that it follows its expected
behavior. A crucial feature of GNATprove is that it interprets annotations
exactly like they are interpreted at run-time during tests. In particular,
their executable semantics includes the verification of run-time checks, which
can be verified statically with GNATprove.  GNATprove can perform additional
verifications on the specification of the expected behavior itself, and its
correspondance to the code.

Currently, Alfa is only concerned with sequential execution of subprograms. A
future version of Alfa could include support of tasking with restrictions
similar to the ones found in Ravenscar or RavenSPARK. The main features from
Ada absent from Alfa are: exceptions, pointers (access types), controlled types
and interfaces. Each of these features has the potential to make automatic
formal verification impossible, hence their rejection. Note that, in many
cases, ad-hoc data structures based on pointers can be replaced by the use of
standard Ada containers (vectors, lists, sets, maps, etc.) Although standard
containers are not in Alfa, we have defined a slightly modified version of
these targeted at formal verification. These formal containers are implemented
in the GNAT standard library. These alternative containers are typical of the
tradeoffs implicit in Alfa: favor automatic formal verification as much as
possible, at the cost of minor adaptations to the code.

Alfa is still evolving, so that features not yet supported could be so in the
future. However, the definition and evolution of Alfa should respect the
following principles:

1. Annotations are read-only

No writes to global variables are allowed in annotations (contracts,
assertions, etc.) The possibility of run-time errors in annotations should be
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
subprograms partially in Alfa.

A consequence of this definition is that a subprogram fully in Alfa can only
call subprograms that are themselves partially or fully in Alfa. A subprogram
partially or not in Alfa can call any kind of subprogram. Further restrictions
apply to calls in annotations.

Most formal verification activities performed with GNATprove address
subprograms that are fully in Alfa. Some activities, which apply to the
contract of the subprogram only, also address subprograms that are partially in
Alfa.

Automatic Detection of Subprograms in Alfa
------------------------------------------

GNATprove automatically detects which subprograms are fully in Alfa, and which
subprograms are either not in Alfa or only partially in Alfa. Thus, the user
does not have to annotate the code to provide this information. However, the
user can review the results of this automatic detection, and require that some
subprograms are fully in Alfa (leading to an error if not).

Summary File
^^^^^^^^^^^^

The information of which subprograms are fully in Alfa and which are not is
stored in a file with extension .alfa for review by the user. For those
subprograms not fully in Alfa, it also records in the same file whether:

* the subprogram uses constructs not in Alfa (e.g. access types);
* the subprogram uses constructs in Alfa but not yet implemented.

In the second case, GNATprove also outputs when possible more precise
information on the features that should be implemented so that this subprogram
is fully in Alfa:

* slice: array slices;
* container: formal containers;
* discriminant: discriminant records;
* dispatch: dispatching;
* block statement: block declare statements;
* generic: generics;
* impure function: functions which write to global variables.
* tagged: tagged types

As an example, consider the following code::

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

    -p__set p.adb:2
    -p__p0__get p.adb:10
    +p__p0__p1 p.adb:15
    +p__p0 p.adb:7

The first character denotes whether the subprogram is fully in Alfa (+) or not
(-).  The name that follows is a unique name for the subprogram. The location
of the subprogram is given next with its file and line. Subprograms not fully
in Alfa may be followed by a set of features not yet implemented in
parentheses, whose implementation would make the subprogram in Alfa.

In the example above, P.Set and P.P0.Get are both partially in Alfa only
because their bodies both contain pointer dereferences. P.P0.P1 is fully in
Alfa. Since P.Set is partially in Alfa and P.P0.P1 is fully in Alfa, P.P0 is
fully in Alfa. 

The purpose of the additional information on features not yet implemented is to
allow users to experiment and see which features are more beneficial in their
context, in order to prioritize efficiently their implementation.

User-specified Compliance
^^^^^^^^^^^^^^^^^^^^^^^^^

The user may require that some subprograms are in Alfa by inserting a specific
pragma ``Annotate`` in the body of the subprogram. He may also insert this
pragma in a package declaration (spec or body) to require that all subprogram
declarations in this package (spec or body) are in Alfa.

On the following example::

    package P is
       pragma Annotate (gnatprove, Force);
       X : access Boolean;
       procedure P0;
    end P;

    package body P is
       pragma Annotate (gnatprove, Force);

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

    p.adb:6:07: explicit dereference is not in Alfa
    p.ads:3:08: access type is not in Alfa

The error messages distinguish constructs not in Alfa (like a pointer
dereference) from constructs not yet implemented. Notice that no error is given
for the dereference in P.P0.Get, as another pragma Annotate in that subprogram
specifies that formal proof should not be done on this subprogram.

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

Known Bounds for Scalar Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The bounds of base types for user-defined types, which define which
computations overflow, may vary depending on the compiler and host/target
architectures. In Alfa, all bounds should be set to their minimum range
guaranteed by the Ada standard (worst case). For example, the following type
should have a base type ranging from -10 to 10 (standard requires a symmetric
range with a possible extra negative value)::

    type T is 1 .. 10;

This other type should have a base type ranging from -10 to 9::

    type T is -10 .. 1;

The bounds of standard scalar types are defined by the GNAT compiler for every
host/target architecture.

No Compiler Permissions
^^^^^^^^^^^^^^^^^^^^^^^

Ada standard defines various ways in which a compiler is allowed to compute a
correct result for a computation instead of raising a run-time error. In Alfa,
we reject all such permissions and interpret all computations with the
strictest meaning.

Pure Specifications
-------------------

Specifications should have a pure logical meaning and no visible effect on the
computation, aside from possibly raising an exception at run-time when
ill-defined (run-time error) or invalid (assertion violation). This is
guaranteed in Alfa by the restriction that functions should not perform writes
to global variables.

Current Definition of Alfa
--------------------------

As indicated before, tasking is excluded from Alfa, as well as exceptions,
pointers (access types), controlled types and interfaces. Features of Ada for
object-oriented programming and generic programming are included in Alfa:
tagged types, dispatching, generics. Compared to SPARK, restrictions in Alfa do
not target increase in readability, so use-clause, overloading and renamings
are allowed for example. Also compared to SPARK, restrictions in Alfa do not
constrain control flow, so arbitrary exits from loops and returns in
subprograms are allowed. Note that these restrictions can be detected with a
coding style checker like GNATcheck. The following sections go into more
details about what is or not in Alfa.

Function Calls in Annotations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The contracts of functions called in annotations are essential for automatic
proofs. The current translation scheme in GNATprove could introduce
inconsistent axioms for incorrect function contracts, so we restrict calls in
annotations to expression functions only. The syntax of expression functions,
introduced in Ada 2012, allows defining functions whose implementation simply
returns an expression. For such expression functions to be called in
annotations in Alfa, they must not have contracts and only call other
expression functions with the same qualities, and no recursion is allowed
between them::

    function Even (X : Integer) return Boolean is (X mod 2 = 0);

    function Odd (X : Integer) return Boolean is (not Even (X));

    function Is_Prime (X : Integer) with
      Pre => Is_Odd (X);

Calls to Standard Library Functions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Standard library functions are conservatively assumed to write to globals, so
they are not currently in Alfa. Note that this does not apply to procedures
from the standard library. It will require a pre-analysis of the standard
library to define proper contracts.

Loop Invariants
^^^^^^^^^^^^^^^

In order for GNATprove to prove formally the properties of interest on
subprograms with loops, the user should annotate these loops with loop
invariants. A loop invariant gives information on the state at entry to the
loop at each iteration. Loop invariants in Alfa consist in the conjunction of
all assertions that appear at the beginning of the loop body. Loop invariants
may have to be precise enough to prove the property of interest. For example,
in order to prove the postcondition of function ``Contains`` below, one has to 
write a precise loop invariant such as the one given below::

  function Contains (Table : IntArray; Value : Integer) return Boolean with
    Post => (for some J in Table'Range => Table(J) = Value);

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
``Src'Loop_Entry`` such as the one given below::

  procedure Move (Dest, Src : out IntArray) with
    Post => (for all J in Dest'Range => Dest (J) = Src'Old (J));

  procedure Move (Dest, Src : out IntArray) is
  begin
     for Index in Dest'Range loop
        pragma Assert (for all J in Dest'First .. Index - 1 =>
                         Dest (J) = Src'Loop_Entry (J));

        Dest (Index) := Src (Index);
        Src (Index) := 0;
     end loop;
  end Move;

Features Not Yet Implemented
----------------------------

The major features not yet implemented are:

* OO programming: tagged types, dispatching
* generics
* formal containers
* invariants on types (invariants and predicates)

Minor features not yet implemented are:

* discriminant / variant records
* array slices
* declare block statements
* elaboration code
* many corner cases in expressions
* attribute ``'Loop_Entry``
