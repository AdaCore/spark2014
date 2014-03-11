.. _Appendix:

********
Appendix
********

.. _command line:

Command-line Options
====================

|GNATprove| is executed with the following command line::

 Usage: gnatprove -Pproj [files] [switches] [-cargs switches]
 proj is a GNAT project file
 files is one or more file names
 -cargs switches are passed to gcc

 gnatprove basic switches:
 -f                 Force recompilation/analysis of all units
 -jnnn              Use nnn parallel processes (default: 1)
 -k                 Do not stop analysis at the first error
     --mode=m       Set the mode of GNATprove (m=check, flow, prove, all*)
 -q, --quiet        Be quiet/terse
     --clean        Remove GNATprove intermediate files, and exit
     --report=r     Set the report mode of GNATprove (r=fail*, all, statistics)
 -u                 Unique analysis. Only analyze the given units
 -U                 Analyze all units of all projects
 -v, --verbose      Output extra verbose information
     --version      Output version of the tool and exit
     --warnings=w   Set the warning mode of GNATprove (w=off, on, error*)
 -h, --help         Display this usage information

 * Main mode values
   . check - Check SPARK restrictions for code where SPARK_Mode=On
   . flow  - Prove object initialization and flow contracts
   . prove - Prove subprogram contracts and absence of run-time errors
   . all   - Activates all modes (default)

 * Report mode values
   . fail       - Report failures to prove checks (default)
   . all        - Report all results of proving checks
   . statistics - Same as all, plus timing and steps information

 * Warning mode values
   . off   - Do not issue warnings
   . on    - Issue warnings
   . error - Treat warnings as errors (default)

 gnatprove advanced switches:
 -d, --debug        Debug mode
 --flow-debug       Extra debugging for flow analysis (requires graphviz)
     --proof=p      Set the proof mode (p=per_check*, per_path, progressive)
     --RTS=dir      Specify the Ada runtime name/location
     --pedantic     Use a strict interpretation of the Ada standard
     --steps=nnn    Set the maximum number of proof steps to nnn for Alt-Ergo
     --timeout=s    Set the prover timeout in seconds (default: 1)
     --limit-line=s Limit analysis to given file and line
     --limit-subp=s Limit analysis to subprogram defined by file and line
     --prover=s     Use given prover instead of default Alt-Ergo prover

 * Proof mode values
   . per_check   - Generate one formula per check (default)
   . per_path    - Generate one formula per path for each check
   . progressive - Start with one formula per check, then split into
                   paths when needed

.. _Alternative_Provers:

Alternative Provers
===================

|GNATprove| by default uses Alt-Ergo, but it can be used with
different provers, as long as they are supported by the Why3
platform. To use a prover, it must be listed in your ``.why3.conf``
file. The command ``why3config --detect-provers`` can be used to
search your PATH for any supported provers and add them to the config
file. Any such prover can then be used with the ``--prover`` option,
for example:

   ``gnatprove -P foo.gpr --prover=cvc4``

.. _Project_Attributes:

Project Attributes
==================

|GNATprove| reads the package ``Prove`` in the given project file. This package
is allowed to contain an attribute ``Switches``, which defines additional
command line switches that are used for the invokation of |GNATprove|. As an
example, the following package in the project file sets the default report mode
of |GNATprove| to ``all``::

    package Prove is
       for Switches use ("--report=all");
    end Prove;

Switches given on the command line have priority over switches given in the
project file.

Implementation Defined Pragmas
==============================

.. _Pragma_SPARK_Mode:

Pragma ``SPARK_Mode``
---------------------

SPARK_Mode is a three-valued aspect. At least until we get to the
next paragraph, a SPARK_Mode of On, Off, or Auto is associated
with each Ada construct. Roughly, the meaning of the three values is the
following:

 * a value of On means that the construct is required to be in |SPARK|, and
   the construct will be analyzed by |GNATprove|.
 * a value of Off means that the construct will not be analyzed by
   |GNATprove|, and does not need to obey the |SPARK| restrictions. The
   construct also cannot be referenced from other parts that are required to
   be in |SPARK|.
 * a value of Auto means that the construct will not be analyzed, and
   |GNATprove| will infer whether this construct can be used in other |SPARK|
   parts or not.

We now explain in more detail how the SPARK_Mode pragma works.

Some Ada constructs are said to have more than one "section".
For example, a declaration which requires a completion will have (at least)
two sections: the initial declaration and the completion. The SPARK_Modes
of the different sections of one entity may differ. In other words,
SPARK_Mode is not an aspect of an entity but rather of a section of an entity.

For example, if a subprogram declaration has a SPARK_Mode of On while
its body has a SPARK_Mode of Off, then an error would be generated if
the subprogram  took a parameter of an access type but not if
the subprogram declared a local variable of an
access type (recall that access types are not in |SPARK|).

A package is defined to have 4 sections: its visible part, its private part,
its body declarations, and its body statements. Non-package declarations which
require a completion have two sections, as noted above; all other entities and
constructs have only one section.

If the SPARK_Mode of a section of an entity is Off, then the SPARK_Mode
of a later section of that entity shall not be On. [For example, a subprogram
can have a SPARK declaration and a non-SPARK body, but not vice versa.]

If the SPARK_Mode of a section of an entity is Auto, then the SPARK_Mode
of a later section of that entity shall not be On or Off.

The SPARK_Mode aspect can be specified either via a pragma or via an
aspect_specification. In some contexts, only a pragma can be used
because of syntactic limitations. In those contexts where an
aspect_specification can be used, it has the same effect as a
corresponding pragma.

The form of a pragma SPARK_Mode is as follows:

.. code-block:: ada

   pragma SPARK_Mode [ (On | Off) ]

The form for the aspect_definition of a SPARK_Mode aspect_specification is
as follows:

.. code-block:: ada

   [ On | Off ]

For example:

.. code-block:: ada

   package P
      with SPARK_Mode => On
   is

The pragma can be used as a configuration pragma. The effect of
such a configuration pragma is described below in the rules for
determining the SPARK_Mode aspect value for an arbitrary section of an
arbitrary Ada entity or construct.

Pragma ``SPARK_Mode`` shall be used as a local pragma in only the following
contexts and has the described semantics:

* When the pragma appears at the start of the visible declarations (preceded
  only by other pragmas) of a package declaration, it specifies the
  SPARK_Mode aspect of the visible part of the package. This can also
  be accomplished via a SPARK_Mode aspect specification as part of the
  package_specification.

* When the pragma appears at the start of the private declarations of a
  package (only other pragmas can appear between the ``private`` keyword
  and the ``SPARK_Mode`` pragma), it specifies the SPARK_Mode aspect
  of the private part of the package. [This cannot be accomplished via
  an aspect_specification.]

* When the pragma appears immediately at the start of the declarations of a
  package body (preceded only by other pragmas),
  it specifies the SPARK_Mode aspect of the body declarations of the package.
  This can also be accomplished via a SPARK_Mode aspect specification
  as part of the package_body.

* When the pragma appears at the start of the elaboration statements of
  a package body (only other pragmas can appear between the ``begin``
  keyword and the ``SPARK_Mode`` pragma),
  it specifies the SPARK_Mode aspect of the body
  statements of the package. [This cannot be accomplished via
  an aspect_specification.]

* When the pragma appears after a subprogram declaration (with only other
  pragmas intervening), it specifies the SPARK_Mode aspect of the
  subprogram's specification. This can also be accomplished via a SPARK_Mode
  aspect_specification as part of the subprogram_declaration.
  [This does not include the case of a subprogram whose initial declaration
  is via a subprogram_body_stub. Such a subprogram has only one section
  because a subunit is not a completion.]

* When the pragma appears at the start of the declarations of a subprogram
  body (preceded only by other pragmas), it specifies the SPARK_Mode aspect
  of the subprogram's body. This can also be accomplished via a SPARK_Mode
  aspect_specification as part of the subprogram_body.

A default argument of On is assumed for any SPARK_Mode pragma or
aspect_specification for which no argument is explicitly specified.

A SPARK_Mode of Auto cannot be explicitly specified; the
cases in which a SPARK_Mode of Auto is implicitly specified are
described below. Roughly speaking, Auto indicates that it is left up to
the formal verification tools to determine whether or not a given construct
is in |SPARK|.

A SPARK_Mode pragma or aspect specification shall only apply to a
(section of a) library-level package or subprogram.

The SPARK_Mode aspect value of an arbitrary section of an arbitrary
Ada entity or construct is then defined to be the following value
(except if this yields a result of Auto for a non-package; see below):

- If SPARK_Mode has been specified for the given section of the
  given entity or construct, then the specified value;

- else for the private part of a package, if SPARK_Mode has been specified
  for the public part of the same package, then the SPARK_Mode of
  the public part;

- else for a package body statements, if SPARK_Mode has been specified for the
  body declarations of the same package, then the SPARK_Mode of the
  body declarations;

- else for any of the visible part or body declarations of a library
  unit package or either section of a library unit subprogram,
  if there is an applicable SPARK_Mode configuration pragma then the
  value specified by the pragma; if no such configuration pragma
  applies, then an implicit specification of Auto is assumed;

- else the SPARK_Mode of the enclosing section of the nearest enclosing
  package or subprogram;

- Corner cases: the SPARK_Mode of the visible declarations of the
  limited view of a package is always Auto; the SPARK_Mode of any
  section of a generic library unit is On.
  [Recall that any generic unit is in |SPARK|.]

If the above computation yields a result of Auto for any construct
other than one of the four sections of a package, then a result of On
or Off is determined instead based on the legality (with respect to
the rules of |SPARK|) of the construct. The construct's SPARK_Mode is
On if and only if the construct is in |SPARK|. [A SPARK_Mode of Auto
is therefore only possible for (sections of) a package.]

In code where SPARK_Mode is On (also called "SPARK code"), the rules of
|SPARK| are enforced. In particular, such code shall not reference
non-SPARK entities, although such code may reference a SPARK declaration
with one or more non-SPARK subsequent sections (e.g., a package whose
visible part has a SPARK_Mode of On but whose private part has a SPARK_Mode
of Off; a package whose visible part has a SPARK_Mode of Auto may also be
referenced).
Similarly, code where SPARK_Mode is On shall not enclose code where
SPARK_Mode is Off unless the non-SPARK code is part of the "completion"
(using that term imprecisely, because we are including the private
part of a package as part of its "completion" here) of a SPARK declaration.

SPARK_Mode is an implementation-defined Ada aspect; it is not (strictly
speaking) part of the |SPARK| language. It is used to notionally transform
programs which would otherwise not be in |SPARK| so that they can
be viewed (at least in part) as |SPARK| programs.

Note that if you would like to mark all your code in SPARK_Mode, the
simplest solution is to specify in your project file::

   package Builder is
      for Global_Configuration_Pragmas use "spark.adc";
   end Builder;

and provide a file `spark.adc` which contains::

   pragma SPARK_Mode;

.. _GNATprove_Limitations:

|GNATprove| Limitations
=======================

Tool Limitations
----------------

#. The Global contracts generated automatically by |GNATprove| for subprograms
   without an explicit one do not take into account indirect calls (through
   access-to-subprogram and dynamic binding) and indirect reads/writes to
   global variables (through access variables).

#. Defining multiple units in the same file is not supported. Instead,
   define each unit in a separate file. You can use the gnatchop tool to
   automate this.

#. |GNATprove| automatically re-analyzes source files when they have changed,
   or when compilation options have changed. However, |GNATprove| does not
   detect changes in target configuration files and pragma configuration
   files. Use option ``-f`` in that case.

#. A subset of all Ada fixed-point types and fixed-point operations is
   supported:

   * fixed-point types must have a small that is a negative power of 2 or 10
   * multiplication and division between different fixed-point types and
     universal real are rejected
   * multiplication and division whose result type is not the same fixed-point
     type as its fixed-point argument(s) are rejected

   These restrictions ensure that the result of fixed-point operations always
   belongs to the *perfect result set* as defined in Ada RM G.2.3.

Legality Rules
--------------

#. |SPARK| Reference Manual rule 4.3(1), concerning use of the box
   symbol "<>" in aggregates, is not currently checked.
   
#. The elaboration order rules described in the |SPARK| Reference
   Manual 7.7 are not currently checked.

#. The rule concerned with asserting that all child packages which
   have state denoted as being Part_Of a more visible state
   abstraction are given as constituents in the refinement of the more
   visible state is not checked (|SPARK| Reference Manual rule
   7.2.6(6)).

#. |GNATprove| does not permit formal parameters to be mentioned
   in the ``input_list`` of an Initializes Aspect, contrary
   to |SPARK| Reference Manual 7.1.5(4). This limitation is only
   relevant for packages that are nested inside subprograms.
   This limitation is corrected in versions of the toolset based
   on GNAT Pro 7.2.2, GPL 2014, or later.

Flow Analysis Limitations
-------------------------

#. Flow analysis currently treats all constants, types and array bounds as
   static, as the current language does not allow constants and types to
   appear in global and dependency contracts. The consequence is that
   information flow through constants, type and array bounds is not
   captured by flow analysis.

   Information flow through constants declared locally is captured, but
   only in the subprogram they have been declared in (they are again
   considered to be static objects in nested subprograms).

#. A variable or state abstraction not declared within a package, V,
   which is read during the elaboration of the package, P, but is not
   used in initializing any of the variables or state abstractions P
   (e.g., it could be used in defining the value of a constant) will
   cause a flow error::

      "V" must be listed in the Initializes aspect of "P" (SPARK RM 7.1.5(12))

   To work around this limitation a variable (either visible or hidden
   and represented by a state abstraction) has to be declared in P and
   initialized using V.  This may give rise to a suppressible warning
   that V is not used.

   For example:

   .. code-block:: ada

	pragma SPARK_Mode(On);
	with Q;
	package P
	  with Initializes => (Not_Used => Q.V)
	is
	   -- Attempting to initialize this constant with a variable
	   -- will cause a flow error.
	   -- The work around is to introduce a visible variable as here or
	   -- a state abstraction for a variable declared in the body. In
           -- either case the variable should be initialized using the variable
           -- or state abstraction from the other package.

	   Not_Used : Integer := Q.V;
	   C : constant Integer := Q.V;
	end P;

#. Flow analysis does not yet support calling functions with dependency
   relations. It is possible to annotate a function with a dependency
   relation, but they currently do not have any effect on analysis.

Proof Limitations
-----------------

#. Postconditions of regular functions called in contracts and assertion
   pragmas are not available, possibly leading to unproved checks. The current
   workaround is to use expression functions instead for those functions called
   in contracts and assertion pragmas.

#. Attribute 'Valid is currently assumed to always return True.

#. Values read from an external source are assumed to be valid values.
   Currently there is no model of invalidity or undefinedness.  The onus
   is on the user to ensure that all values read from an external source are
   valid.  The use of an invalid value invalidates any proofs associated with
   the value.

#. Operators are not allowed as actual parameters of a formal container
   instance. Instead, a wrapper expression function can be defined that simply
   calls the operator.

#. The following attributes are not yet supported in proof: Address, Adjacent,
   Aft, Alignment, Bit_Order, Body_Version, Component_Size, Constrained, Copy_Sign,
   Definite, Denorm, First_Bit, First_Valid, Fore, Last_Bit, Last_Valid, Machine,
   all Machine_* attributes, Model, all Model_* attributes, Partition_Id,
   Position, Remainder, Round, Safe_First, Safe_Last, Scale, Scaling,
   Size, Small, Unbiased_Rounding, Version, Wide_Image, Wide_Value,
   Wide_Width, Wide_Wide_Image, Wide_Wide_Value, Wide_Wide_Width,
   Width.

#. The difference between the floating-point values +0 and -0 (as defined in
   IEEE-754 standard) is ignored in proof. This is correct for all programs that
   do not exploit the difference in bit-pattern between +0 and -0. For example,
   the following specially crafted program is proved by |GNATprove| but fails at
   run time due to a division by zero, because function ``Magic`` exploits the
   difference of bit-pattern between +0 and -0 by using ``Unchecked_Conversion``
   to return a different integer value for arguments +0 and -0.

   .. code-block:: ada

      pragma SPARK_Mode;

      with Ada.Unchecked_Conversion;

      procedure Zero_And_Unchecked is
         procedure Crash (A, B : Float) is
            function Magic is new Ada.Unchecked_Conversion (Float, Integer);
            X : Integer;
         begin
            if A = B then
               if Magic (B) /= 0 then
                  X := 100 / Magic (A);
               end if;
            end if;
         end Crash;

         type UInt32 is mod 2 ** 32;
         function Convert is new Ada.Unchecked_Conversion (UInt32, Float);

         Zero_Plus : constant Float := Convert (16#0000_0000#);
         Zero_Neg  : constant Float := Convert (16#8000_0000#);
      begin
         Crash (Zero_Plus, Zero_Neg);
      end Zero_And_Unchecked;


Portability Issues
==================

To execute a |SPARK| program, it is expected that users will compile
the program (as an Ada program) using an Ada compiler.
The SPARK language definition defines a number of implementation-defined
(with respect to the Ada language definition) aspects,
attributes, pragmas, and conventions.
Ideally a |SPARK| program will be compiled using an Ada compiler that
supports all of these constructs. Portability problems may arise
if this is not the case.

This section is a discussion of the strategies available for coping
with this situation.

Probably the most important rule is that pragmas should be used instead
of aspect_specification syntax wherever this option is available. For example,
use pragma Abstract_State rather than specifying the Abstract_State aspect
of a package using aspect_specification syntax. Ada specifies that
unrecognized pragmas shall be ignored, as opposed to being rejected.
This is not the case for (syntactic) aspect specifications
(this terminology is a bit confusing because a pragma can be used to
specify an aspect; such a pragma is semantically, but not syntactically,
an aspect specification).
Furthermore, aspect specification syntax was introduced in Ada 2012
and will be rejected if the program is compiled as, for example, an
Ada 95 program.

Many SPARK-defined constructs have no dynamic semantics (e.g., the Global,
Depends, and Abstract_State aspects), so the run-time behavior of
a program is unaffected if they are ignored by a compiler. Thus, there is
no problem if these constructs are expressed as pragmas which are
then ignored by the Ada compiler.

Of those constructs which do have dynamic semantics, most are run-time
assertions. These include Loop_Variant, Loop_Invariant, Assert_And_Cut,
Contract_Cases, Initial_Condition, and Refined_Postcondition. Because
|SPARK| requires that the success of these assertions must be statically
proven (and that the evaluation of the asserted condition can have no side
effects), the run-time behavior a program is unaffected if they are ignored
by a compiler.

The situation with pragma Assume is slightly different because the
success of the given condition is not statically proven. If ignoring
an Assume pragma at run time is deemed to be unacceptable, then it can
be replaced with an Assert pragma (at the cost of introducing a source
code difference between the |SPARK| program that is analyzed statically
and the Ada program that is executed). An ignored Assume pragma is the
only case where the use of a SPARK-specific construct can lead to a
portability problem which is not detected at compile time. In all
other cases, either the Ada compiler will reject (as opposed to ignore)
an unrecognized construct or the construct can safely be ignored.

An Ada compiler which does not support convention Ghost will reject
any use of this convention. Two safe transformations are available for
dealing with this situation - either replace uses of convention Ghost with
convention Ada or delete the entities declared with a convention of Ghost.
Just as was mentioned above in the case of modifying an Assume pragma,
either choice introduces an analyzed/executed source code difference.

There are two |SPARK| attributes which cannot be used
if they are not supported by the Ada compiler in question: the
Update and Loop_Entry attributes.

|SPARK| includes a rule that a package which declares a state
abstraction requires a body. In the case of a library unit package
(or generic package) which requires a body only because of this rule,
an Ada compiler that knows nothing about state abstractions would
reject the body of the package because of the rule (introduced in Ada 95)
that a library unit package (or generic package) body is never optional;
if it is not required then it is forbidden. In the unlikely event
that this scenario arises in practice, the solution is to force the
library unit package to require a body for some other reason, typically
by adding an Elaborate_Body pragma.

If a |SPARK| program is to be compiled and executed as an Ada 95 program
(or any other pre-2012 version of Ada), then of course any construct
introduced in a later version of Ada must be avoided (unless it is
expressed as a safely-ignored pragma). This seems worth mentioning because
Ada 2012 constructs such as quantified expressions
and conditional expressions are often heavily used in |SPARK| programs.

Semantics of Floating Point Operations
======================================

SPARK assumes that floating point operations are carried out in single
precision (binary32) or double precision (binary64) as defined in the IEEE-754
standard for floating point arithmetic. You should make sure that this is the
case on your platform. For example, on x86 platforms, by default some
intermediate computations may be carried out in extended precision, leading to
unexpected results. With GNAT, you can specify the use of SSE arithmetic by
using the compilation switches "-msse2 -mfpmath=sse" which cause all arithmetic
to be done using the SSE instruction set which only provides 32-bit and 64-bit
IEEE types, and does not provide extended precision. SSE arithmetic is also
more efficient. Note that the ABI allows free mixing of units using the two
types of floating-point, so it is not necessary to force all units in a program
to use SSE arithmetic.

SPARK considers the floating point values which represent positive, negative
infinity or NaN as invalid. Proof obligations are generated that such values
cannot occur.
