.. _Portability Issues:

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
effects), the run-time behavior of a program is unaffected if they are ignored
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
