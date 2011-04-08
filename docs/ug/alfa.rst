ALFA Subset of Ada
==================

Fine-grain Integration with Full-Ada Code
-----------------------------------------

A subprogram spec is in ALFA

A subprogram is in ALFA

Automatic Detection of Subprograms in ALFA
------------------------------------------

GNATprove automatically detects which subprograms are in ALFA, and which
subprograms are not in ALFA. Thus, the user does not have to annotate the code
to provide this information. However, the user can review the results of this
automatic detection, and require that some subprograms are in ALFA (leading to
an error if not).

Summary File
^^^^^^^^^^^^

The information of which subprograms are in ALFA and which are not in ALFA is
stored in a file with extension .alfa for review by the user. For those
subprograms not in ALFA, it also records in the same file whether:

* the subprogram uses constructs definitely not in ALFA;
* the subprogram uses constructs in ALFA but not yet implemented;
* the subprogram uses constructs not currently in ALFA, but that could be added
  to ALFA in the future.

The last case groups various possible extensions:

* slice: allow slices;
* discriminant: allow discriminant records;
* dispatch: allow dispatching;
* block statement: allow block declare statements;
* any return: allow return statements anywhere;
* any exit: allow exit statements anywhere;
* generic: allow generics;
* impure function: allow functions which write to global variables.

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
    -p__p0__p1 p.adb:15 (any return)
    +p__p0 p.adb:7

The first character denotes whether the subprogram is in ALFA (+) or not (-).
The name that follows is a unique name for the subprogram. The location of the
subprogram is given next with its file and line. Subprograms not in ALFA may be
followed by a set of extensions in parentheses, whose implementation would make
the subprogram in ALFA.

In the example above, P.Set and P.P0.Get are not in ALFA because they both
contain pointer dereferences. P.P0.P1 is not in ALFA because it contains a
return statement (not allowed in procedures). However, since P.Set spec and
P.P0.P1 spec are both in ALFA, P.P0 is in ALFA. Notice that implementing the
extension "any return" would put P.P0.P1 in ALFA, hence the parenthesized
extension on the line for P.P0.P1.

The purpose of defining possible extensions early is to allow users to
experiment and see which extensions are more beneficial in their context, in
order to prioritize efficiently their implementation.

User-specified Compliance
^^^^^^^^^^^^^^^^^^^^^^^^^

The user may require that some subprograms are in ALFA by inserting a specific
pragma Annotate in the body of the subprogram. He may also insert this pragma
in a package declaration (spec or body) to require that all subprogram
declarations in this package (spec or body) are in ALFA.

On the following example::

    package P is
       pragma Annotate (Formal_Proof, On);
       X : access Boolean;
       procedure P0;
    end P;

    package body P is
       pragma Annotate (Formal_Proof, On);

       procedure Set is
       begin
	  X.all := True;
       end Set;

       procedure P0 is
	  Y : Boolean;

	  function Get return Boolean is
	     pragma Annotate (Formal_Proof, Off);
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

    p.adb:6:07: explicit dereference is not in ALFA
    p.adb:18:07: "return" in procedure is not yet in ALFA (any return)
    p.adb:21:13: "return" in the middle of subprogram is not yet in ALFA (any return)
    p.ads:3:08: access type is not in ALFA

The error messages distinguish constructs not in ALFA (like a pointer
dereference) from constructs not yet in ALFA (like returns anywhere in a
procedure). Notice that no error is given for the dereference in P.P0.Get, as
another pragma Annotate in that subprogram specifies that formal proof should
not be done on this subprogram.

A Non-ambiguous Subset of Ada
-----------------------------

The behaviour of a program in ALFA should be unique, both in order to
facilitate formal verification of properties over these programs, and to get
the additional guarantee that a formally verified ALFA program always behaves
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

In ALFA, none of these sources of ambiguity is possible.

No Writes to Globals in Functions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In Ada, a sub-expression can write to a global variable through a call. As the
order of evaluation of sub-expressions in an expression (for example, operands
of an arithmetic operation or arguments of a call) is not specified in Ada, the
time of this write may have an influence on the value of the expression. In
ALFA, functions cannot write to globals, which removes this source of
ambiguity.

Parenthesized Arithmetic Operations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In Ada, non-parenthesized arithmetic operations can be re-ordered by the
compiler, which may result in a failing computation (due to overflow checking)
becoming a successful one, and vice-versa. In ALFA, all such operations should
be parenthesized. (SPARK issues a warning on such cases.)

More specifically:

* any operand of a binary adding operation (+,-) that is itself a binary adding
  operation must be parenthesized;
* any operand of a binary multiplying operation (*,/,mod,rem) that is itself a
  binary multiplying operation must be parenthesized.

Known Bounds for Scalar Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The bounds of base types for user-defined types, which define which
computations overflow, may vary depending on the compiler and host/target
architectures. In ALFA, all bounds should be set to their minimum range
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
correct result for a computation instead of raising a run-time error. In ALFA,
we reject all such permissions and interpret all computations with the
strictest meaning.

Pure Specifications
-------------------

Specifications should have a pure logical meaning and no visible effect on the
computation, aside from possibly raising an exception at run-time when
ill-defined (run-time error) or invalid (assertion violation). This is
guaranteed in ALFA by the restriction that functions should not perform writes
to global variables.

Current Definition of ALFA
--------------------------

Possible Extensions
-------------------
