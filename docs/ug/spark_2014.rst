.. _introduction to SPARK:

****************************
Overview of |SPARK| Language
****************************

This chapter provides an overview of the |SPARK| language, detailing for each
feature its consequences in terms of execution and formal verification. This is
not a reference manual for the |SPARK| language, which can be found in:

* the Ada Reference Manual (for Ada features), and
* the |SPARK| Reference Manual (for SPARK-specific features)

More details on how |GNAT Pro| compiles |SPARK| code can be found in the |GNAT
Pro| Reference Manual.

|SPARK| can be seen as a large subset of Ada with additional
aspects/pragmas/attributes, the latest version SPARK 2014 being a much larger
subset than previous versions of |SPARK|. It includes in particular:

* richer types (subtypes with bounds not known statically, discriminant records)
* more flexible features to structure programs (function and operator
  overloading, early returns and exits, raise statements)
* static polymorphism (generics)
* object oriented features (tagged types, dispatching)

In the rest of this chapter, the marker [Ada 2005] (resp. [Ada 2012]) is used
to denote that a feature defined in Ada 2005 (resp. Ada 2012) is supported in
|SPARK|, and the marker [|SPARK|] is used to denote that a feature is specific
to |SPARK|. Both the |GNAT Pro| compiler and |GNATprove| analyzer support all
features listed here.

Language Restrictions
=====================

.. _Excluded Ada Features:

Excluded Ada Features
---------------------

To facilitate formal verification, |SPARK| enforces a number of global
simplifications to Ada 2012. The most notable simplifications are:

* The use of access types and allocators is not permitted. Formal verification
  of programs with pointers requires tracking which memory is allocated and
  which memory has been freed, as well as separation between different blocks
  of memory, which are not doable precisely without a lot of manual work. As a
  replacement, |SPARK| provides rich generic data structures in the
  :ref:`Formal Containers Library`.

* All expressions (including function calls) are free of
  side-effects. Functions with side-effects are more complex to treat logically
  and may lead to non-deterministic evaluation due to conflicting side-effects
  in sub-expressions of an enclosing expression. Functions with side-effects
  should be written as procedures in |SPARK|.

* Aliasing of names is not permitted. Aliasing may lead to unexpected
  interferences, in which the value denoted locally by a given name changes as
  the result of an update to another locally named variable. Formal
  verification of programs with aliasing is less precise and requires more
  manual work. See :ref:`Absence of Interference`.

* The goto statement is not permitted. Gotos can be used to create loops, which
  require a specific treatment in formal verification, and thus should be
  precisely identified. See :ref:`Loop Invariants` and :ref:`Loop Variants`.

* The use of controlled types is not permitted. Controlled types lead to the
  insertion of implicit calls by the compiler. Formal verification of implicit
  calls makes it harder for users to interact with formal verification tools,
  as there is no source code on which information can be reported.

* Handling of exceptions is not permitted. Exception handling gives raise to
  numerous interprocedural control-flow paths. Formal verification of programs
  with exception handlers requires tracking properties along all those paths,
  which is not doable precisely without a lot of manual work. But raising
  exceptions is allowed (see :ref:`Raising Exceptions and Other Error Signaling
  Mechanisms`).

The features listed above are excluded from |SPARK| because, currently, they
defy formal verification. As formal verification technology advances the list
will be revisited and it may be possible to relax some of these
restrictions. There are other features which are technically feasible to
formally verify but which are currently not supported in |SPARK|, most notably
concurrency features (tasks, protected objects, etc.).

Uses of these features in |SPARK| code are detected by |GNATprove| and reported
as errors. Formal verification is not possible on subprograms using these
features. But these features can be used in subprograms in Ada not identified
as |SPARK| code, see :ref:`Identifying SPARK Code`.

Partially Analyzed Ada Features
-------------------------------

|SPARK| reinforces the strong typing of Ada with a stricter initialization
policy (see :ref:`Data Initialization Policy`), and thus provides no means
currently of specifying that some input data may be invalid. As a result, the
following features are allowed in |SPARK|, but only partially analyzed by
|GNATprove|:

* The result of a call to ``Unchecked_Conversion`` is assumed to be a valid
  value of the resulting type.

* The evaluation of attribute ``Valid`` is assumed to always return True.

This is illustrated in the following example:

.. literalinclude:: gnatprove_by_example/examples/validity.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/validity.adb
   :language: ada
   :linenos:

|GNATprove| proves both assertions, but issues warnings about its assumptions
that the evaluation of attribute ``Valid`` on both input parameter ``X`` and
the result of the call to ``Unchecked_Conversion`` return True:

.. literalinclude:: gnatprove_by_example/results/validity.prove
   :language: none

.. _Data Initialization Policy:

Data Initialization Policy
--------------------------

Modes on parameters and data dependency contracts (see :ref:`Data
Dependencies`) in |SPARK| have a stricter meaning than in Ada:

* Parameter mode ``in`` (resp. global mode ``Input``) indicates that the
  object denoted in the parameter (resp. data dependencies) should be
  completely initialized before calling the subprogram. It should not be
  written in the subprogram.

* Parameter mode ``out`` (resp. global mode ``Output``) indicates that the
  object denoted in the parameter (resp. data dependencies) should be
  completely initialized before returning from the subprogram. It should not
  be read in the program prior to initialization.

* Parameter mode ``in out`` (resp. global mode ``In_Out``) indicates that the
  object denoted in the parameter (resp. data dependencies) should be
  completely initialized before calling the subprogram. It can be written in
  the subprogram.

* Global mode ``Proof_In`` indicates that the object denoted in the data
  dependencies should be completely initialized before calling the
  subprogram. It should not be written in the subprogram, and only read in
  contracts and assertions.

Hence, all inputs should be completely initialized at subprogram entry, and all
outputs should be completely initialized at subprogram output. Similarly, all
objects should be completely initialized when read (e.g. inside subprograms),
at the exception of record subcomponents (but not array subcomponents) provided
the subcomponents that are read are initialized.

A consequence of the rules above is that a parameter (resp. global variable)
that is partially written in a subprogram should be marked as ``in out``
(resp. ``In_Out``), because the input value of the parameter (resp. global
variable) is `read` when returning from the subprogram.

|GNATprove| will issue check messages if a subprogram does not respect the
aforementioned data initialization policy. For example, consider a procedure
``Proc`` which has a parameter and a global item of each mode:

.. literalinclude:: gnatprove_by_example/examples/data_initialization.ads
   :language: ada
   :linenos:

Procedure ``Proc`` should completely initialize its outputs ``P2`` and ``G2``,
but it only initalizes them partially. Similarly, procedure ``Call_Proc`` which
calls ``Proc`` should completely initalize all of ``Proc``'s inputs prior to
the call, but it only initalizes ``G1`` completely.

.. literalinclude:: gnatprove_by_example/examples/data_initialization.adb
   :language: ada
   :linenos:

On this program, |GNATprove| issues 6 high check messages, corresponding to
the violations of the data initialization policy:

.. literalinclude:: gnatprove_by_example/results/data_initialization.flow
   :language: none

While a user can justify individually such messages with pragma ``Annotate``
(see section :ref:`Justifying Check Messages`), it is under her responsibility
to then ensure correct initialization of subcomponents that are read, as
|GNATprove| relies during proof on the property that data is properly
initialized before being read.

Note also the various warnings that |GNATprove| issues on unused parameters,
global items and assignments, also based on the stricter |SPARK| interpretation
of parameter and global modes.

.. _Absence of Interference:

Absence of Interference
-----------------------

In |SPARK|, an assignment to a variable cannot change the value of another
variable. This is enforced by forbidding the use of access types (pointers) in
|SPARK|, and by restricting aliasing between parameters and global variables so
that only benign aliasing is accepted (i.e. aliasing that does not cause
interference).

The precise rules detailed in SPARK RM 6.4.2 can be summarized as follows:

* Two output parameters should never be aliased.
* An input and an output parameters should not be aliased, unless the input
  parameter is always passed by copy.
* An output parameter should never be aliased with a global variable referenced
  by the subprogram.
* An input parameter should not be aliased with a global variable referenced by
  the subprogram, unless the input parameter is always passed by copy.

These rules extend the existing rules in Ada RM 6.4.1 for restricting aliasing,
which already make it illegal to call a procedure with problematic (non-benign)
aliasing between parameters of scalar type that are `known to denote the same
object` (a notion formally defined in Ada RM).

For example, in the following example:

.. literalinclude:: gnatprove_by_example/examples/aliasing.ads
   :language: ada
   :linenos:

Procedure ``Whatever`` can only be called on arguments that satisfy the
following constraints:

1. Arguments for ``Out_1`` and ``Out_2`` should not be aliased.
2. Variable ``Glob`` should not be passed in argument for ``Out_1`` and ``Out_2``.

Note that there are no constraints on input parameters ``In_1`` and ``In_2``,
as these are always passed by copy (being of a scalar type). This would not be
the case if these input parameters were of a record or array type.

For example, here are examples of correct and illegal (according to Ada and
SPARK rules) calls to procedure ``Whatever``:

.. literalinclude:: gnatprove_by_example/examples/check_param_aliasing.adb
   :language: ada
   :linenos:

|GNATprove| (like |GNAT Pro| compiler, since these are also Ada rules)
correctly detects the two illegal calls and issues errors:

.. literalinclude:: gnatprove_by_example/results/check_param_aliasing.flow
   :language: none

Here are other examples of correct and incorrect calls (according to SPARK
rules) to procedure ``Whatever``:

.. literalinclude:: gnatprove_by_example/examples/check_aliasing.adb
   :language: ada
   :linenos:

|GNATprove| correctly detects the two incorrect calls and issues error
messages:

.. literalinclude:: gnatprove_by_example/results/check_aliasing.flow
   :language: none

.. _Raising Exceptions and Other Error Signaling Mechanisms:

Raising Exceptions and Other Error Signaling Mechanisms
-------------------------------------------------------

Raising an exception is allowed in |SPARK| to signal an error, but handling the
exception raised to perform recovery or mitigation actions is outside of the
|SPARK| subset. Typically, such exception handling code should be added to
top-level subprograms in full Ada, or to a last chance handler called by the
runtime when an exception is raised, none of which is analyzed by |GNATprove|.

|GNATprove| treats raising an exception specially:

 * in flow analysis, the program paths that lead to a ``raise_statement`` are
   not considered when checking the contract of the subprogram, which is only
   concerned with executions that terminate normally; and
 * in proof, a check is generated for each ``raise_statement``, to prove that
   no such program point is reachable.

Multiple error signaling mechanisms are treated the same way:

 * raising an exception
 * ``pragma Assert (X)`` where ``X`` is an expression statically equivalent to
   ``False``
 * calling a subprogram with an aspect or pragma ``No_Return`` that has no
   outputs

For example, consider the artificial subprogram ``Check_OK`` which raises an
exception when parameter ``OK`` is ``False``:

.. literalinclude:: gnatprove_by_example/examples/abnormal_terminations.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/abnormal_terminations.adb
   :language: ada
   :linenos:

Note that, although ``G2`` is assigned in ``Check_OK``, its assignment
is directly followed by a ``raise_statement``, so ``G2`` is never
assigned on an execution of ``Check_OK`` that terminates normally. As
a result, ``G2`` is not mentioned in the data dependencies of
``Check_OK``. During flow analysis, |GNATprove| verifies that the body of
``Check_OK`` implements its declared data dependencies.

During proof, |GNATprove| generates a check that the
``raise_statement`` on line 11 is never reached. Here, it is proved
thanks to the precondition of ``Check_OK`` which states that parameter
``OK`` should always be ``True`` on entry:

.. literalinclude:: gnatprove_by_example/results/abnormal_terminations.prove
   :language: none

|GNATprove| also checks that procedures that are marked with aspect or pragma
``No_Return`` do not return: they should either raise an exception or loop
forever on any input.

.. _Subprogram Contracts:

Subprogram Contracts
====================

The most important feature to specify the intended behavior of a |SPARK|
program is the ability to attach a contract to subprograms. This contract is
made up of various optional parts:

* The `precondition` introduced by aspect ``Pre`` specifies constraints on
  callers of the subprogram.
* The `postcondition` introduced by aspect ``Post`` specifies (partly or
  completely) the functional behavior of the subprogram.
* The `contract cases` introduced by aspect ``Contract_Cases`` is a way to
  partition the behavior of a subprogram. It can replace or complement a
  precondition and a postcondition.
* The `data dependencies` introduced by aspect ``Global`` specify the global
  data read and written by the subprogram.
* The `flow dependencies` introduced by aspect ``Depends`` specify how
  subprogram outputs depend on subprogram inputs.

Which contracts to write for a given verification objective, and how
|GNATprove| generates default contracts, is detailed in :ref:`How to Write
Subprogram Contracts`.

The contract on a subprogram describes the behavior of successful
calls. Executions that end up by signalling an error, as described in
:ref:`Raising Exceptions and Other Error Signaling Mechanisms`, are not covered
by the subprogram's contract. A call to a subprogram is successful if execution
terminates normally, or if execution loops without errors for a subprogram
marked with aspect ``No_Return`` that has some outputs (this is typically the
case of a non-terminating subprogram implementing the main loop of a
controller).

.. _Preconditions:

Preconditions
-------------

[Ada 2012]

The precondition of a subprogram specifies constraints on callers of the
subprogram. Typically, preconditions are written as conjunctions of constraints
that fall in one of the following categories:

* exclusion of forbidden values of parameter, for example ``X /= 0`` or ``Y not
  in Active_States``
* specification of allowed parameter values, for example ``X in 1 .. 10`` or
  ``Y in Idle_States``
* relations that should hold between parameter values, for example ``(if Y in
  Active_State then Z /= Null_State)``
* expected values of global variables denoting the state of the computation,
  for example ``Current_State in Active_States``
* invariants about the global state that should hold when calling this
  subprogram, for example ``Is_Complete (State_Mapping)``
* relations involving the global state and input parameters that should hold
  when calling this subprogram, for example ``X in Next_States (Global_Map,
  Y)``

When the program is compiled with assertions (for example with switch
``-gnata`` in |GNAT Pro|), the precondition of a subprogram is checked at run
time every time the subprogram is called. An exception is raised if the
precondition fails. Not all assertions need to be enabled though. For example,
a common idiom is to enable only preconditions (and not other assertions) in
the production binary, by setting pragma ``Assertion_Policy`` as follows:

.. code-block:: ada

   pragma Assertion_Policy (Pre => Check);

When a subprogram is analyzed with |GNATprove|, its precondition is used to
restrict the contexts in which it may be executed, which is required in general
to prove that the subprogram's implementation:

* is free from run-time errors (see :ref:`Writing Contracts for Program
  Integrity`); and
* ensures that the postcondition of the subprogram always holds (see
  :ref:`Writing Contracts for Functional Correctness`).

In particular, the default precondition of ``True`` used by |GNATprove| when no
explicit one is given may not be precise enough, unless it can be analyzed in
the context of its callers by |GNATprove| (see :ref:`Contextual Analysis of
Subprograms Without Contracts`). When a caller is analyzed with |GNATprove|, it
checks that the precondition of the called subprogram holds at the point of
call. And even when the implementation of the subprogram is not analyzed with
|GNATprove|, it may be necessary to add a precondition to the subprogram for
analyzing its callers (see :ref:`Writing Contracts on Imported Subprograms`).

For example, consider the procedure ``Add_To_Total`` which increments global
counter ``Total`` by the value given in parameter ``Incr``. To ensure that
there are no integer overflows in the implementation, ``Incr`` should not be
too large, which a user can express with the following precondition:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Pre => Incr >= 0 and then Total <= Integer'Last - Incr;

To ensure that the value of ``Total`` remains non-negative, one should also add
the condition ``Total >= 0`` to the precondition:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Pre => Incr >= 0 and then Total in 0 .. Integer'Last - Incr;

Finally, |GNATprove| also analyzes preconditions to ensure that they are free
from run-time errors in all contexts. This may require writing the precondition
in a special way. For example, the precondition of ``Add_To_Total`` above uses
the shorcut boolean operator ``and then`` instead of ``and``, so that calling
the procedure in a context where ``Incr`` is negative does not result in an
overflow when evaluating ``Integer'Last - Incr``. Instead, the use of ``and
then`` ensures that a precondition failure will occur before the expression
``Integer'Last - Incr`` is evaluated.

.. note::

   It is good practice to use the shortcut boolean operator ``and then``
   instead of ``and`` in preconditions. This is required in some cases by
   |GNATprove| to prove absence of run-time errors inside preconditions.

.. _Postconditions:

Postconditions
--------------

[Ada 2012]

The postcondition of a subprogram specifies partly or completely the functional
behavior of the subprogram. Typically, postconditions are written as
conjunctions of properties that fall in one of the following categories:

* possible values returned by a function, using the special attribute
  ``Result`` (see :ref:`Attribute Result`), for example ``Get'Result in
  Active_States``
* possible values of output parameters, for example ``Y in Active_States``
* expected relations between output parameter values, for example ``if Success
  then Y /= Null_State``
* expected relations between input and output parameter values, possibly using
  the special attribute ``Old`` (see :ref:`Attribute Old`), for example ``if
  Success then Y /= Y'Old``
* expected values of global variables denoting updates to the state of the
  computation, for example ``Current_State in Active_States``
* invariants about the global state that should hold when returning from this
  subprogram, for example ``Is_Complete (State_Mapping)``
* relations involving the global state and output parameters that should hold
  when returning from this subprogram, for example ``X in Next_States
  (Global_Map, Y)``

When the program is compiled with assertions (for example with switch
``-gnata`` in |GNAT Pro|), the postcondition of a subprogram is checked at run
time every time the subprogram returns. An exception is raised if the
postcondition fails. Usually, postconditions are enabled during tests, as they
provide dynamically checkable oracles of the intended behavior of the program,
and disabled in the production binary for efficiency.

When a subprogram is analyzed with |GNATprove|, it checks that the
postcondition of a subprogram cannot fail. This verification is modular:
|GNATprove| considers all calling contexts in which the precondition of the
subprogram holds for the analysis of a subprogram. |GNATprove| also analyzes
postconditions to ensure that they are free from run-time errors, like any
other assertion.

For example, consider the procedure ``Add_To_Total`` which increments global
counter ``Total`` with the value given in parameter ``Incr``. This intended
behavior can be expressed in its postcondition:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => Total = Total'Old + Incr;

The postcondition of a subprogram is used to analyze calls to the
subprograms. In particular, the default postcondition of ``True`` used by
|GNATprove| when no explicit one is given may not be precise enough to prove
properties of its callers, unless it analyzes the subprogam's implementation in
the context of its callers (see :ref:`Contextual Analysis of Subprograms
Without Contracts`).

Recursive subprograms and mutually recursive subprograms are treated in this
respect exactly like non-recursive ones. Provided the execution of these
subprograms always terminates (a property that is not verified by |GNATprove|),
then |GNATprove| correctly checks that their postcondition is respected by
using this postcondition for recursive calls.

Special care should be exercized for functions that return a boolean, as a
common mistake is to write the expected boolean result as the postcondition:

.. code-block:: ada

   function Total_Above_Threshold (Threshold : in Integer) return Boolean with
     Post => Total > Threshold;

while the correct postcondition uses :ref:`Attribute Result`:

.. code-block:: ada

   function Total_Above_Threshold (Threshold : in Integer) return Boolean with
     Post => Total_Above_Threshold'Result = Total > Threshold;

Both |GNAT Pro| compiler and |GNATprove| issue a warning on the semantically
correct but likely functionally wrong postcondition.

.. _Contract Cases:

Contract Cases
--------------

[|SPARK|]

When a subprogram has a fixed set of different functional behaviors, it may be
more convenient to specify these behaviors as contract cases rather than a
postcondition. For example, consider a variant of procedure ``Add_To_Total``
which either increments global counter ``Total`` by the given parameter value
when possible, or saturates at a given threshold. Each of these behaviors can
be defined in a contract case as follows:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Contract_Cases => (Total + Incr < Threshold  => Total = Total'Old + Incr,
                        Total + Incr >= Threshold => Total = Threshold);

Each contract case consists in a guard and a consequence separated by the
symbol ``=>``. When the guard evaluates to ``True`` on subprogram entry, the
corresponding consequence should also evaluate to ``True`` on subprogram
exit. We say that this contract case was enabled for the call. Exactly one
contract case should be enabled for each call, or said equivalently, the
contract cases should be disjoint and complete.

For example, the contract cases of ``Add_To_Total`` express that the subprogram
should be called in two distinct cases only:

* on inputs that can be added to ``Total`` to obtain a value strictly less than
  a given threshold, in which case ``Add_To_Total`` adds the input to
  ``Total``.
* on inputs whose addition to ``Total`` exceeds the given threshold, in which
  case ``Add_To_Total`` sets ``Total`` to the threshold value.

When the program is compiled with assertions (for example with switch
``-gnata`` in |GNAT Pro|), all guards are evaluated on entry to the subprogram,
and there is a run-time check that exactly one of them is ``True``. For this
enabled contract case, there is another run-time check when returning from the
subprogram that the corresponding consequence evaluates to ``True``.

When a subprogram is analyzed with |GNATprove|, it checks that there is always
exactly one contract case enabled, and that the consequence of the contract
case enabled cannot fail. If the subprogram also has a precondition,
|GNATprove| performs these checks only for inputs that satisfy the
precondition, otherwise for all inputs.

In the simple example presented above, there are various ways to express an
equivalent postcondition, in particular using :ref:`Conditional Expressions`:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => (if Total'Old + Incr < Threshold  then
                Total = Total'Old + Incr
              else
                Total = Threshold);

   procedure Add_To_Total (Incr : in Integer) with
     Post => Total = (if Total'Old + Incr < Threshold then Total'Old + Incr else Threshold);

   procedure Add_To_Total (Incr : in Integer) with
     Post => Total = Integer'Min (Total'Old + Incr, Threshold);

In general, an equivalent postcondition may be cumbersome to write and less
readable. Contract cases also provide a way to automatically verify that the
input space is partitioned in the specified cases, which may not be obvious
with a single expression in a postcondition when there are many cases.

The guard of the last case may be ``others``, to denote all cases not captured
by previous contract cases. For example, the contract of ``Add_To_Total`` may
be written:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Contract_Cases => (Total + Incr < Threshold => Total = Total'Old + Incr,
                        others                   => Total = Threshold);

When ``others`` is used as a guard, there is no need for verification (both at
run-time and using |GNATprove|) that the set of contract cases covers all
possible inputs. Only disjointness of contract cases is checked in that case.

.. _Data Dependencies:

Data Dependencies
-----------------

[|SPARK|]

The data dependencies of a subprogram specify the global data that a subprogram
is allowed to read and write. Together with the parameters, they completely
specify the inputs and outputs of a subprogram. Like parameters, the global
variables mentioned in data dependencies have a mode: ``Input`` for inputs,
``Output`` for outputs and ``In_Out`` for global variables that are both inputs
and outputs. A last mode of ``Proof_In`` is defined for inputs that are only
read in contracts and assertions. For example, data dependencies can be
specified for procedure ``Add_To_Total`` which increments global counter
``Total`` as follows:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Global => (In_Out => Total);

Data dependencies have no impact on compilation and the run-time behavior of a
program. When a subprogram is analyzed with |GNATprove|, it checks that the
implementation of the subprogram:

* only reads global inputs mentioned in its data dependencies,
* only writes global outputs mentioned in its data dependencies, and
* always completely initializes global outputs that are not also inputs.

See :ref:`Data Initialization Policy` for more details on this analysis of
|GNATprove|. During its analysis, |GNATprove| uses the specified data
dependencies of callees to analyze callers, if present, otherwise a default
data dependency contract is generated (see :ref:`Generation of Dependency
Contracts`) for callees.

There are various benefits when specifying data dependencies on a subprogram,
which gives various reasons for users to add such contracts:

* |GNATprove| verifies automatically that the subprogram implementation
  respects the specified accesses to global data.
* |GNATprove| uses the specified contract during flow analysis, to analyze the
  data and flow dependencies of the subprogram's callers, which may result in a
  more precise analysis (less false alarms) than with the generated data
  dependencies.
* |GNATprove| uses the specified contract during proof, to check absence of
  run-time errors and the functional contract of the subprogram's callers,
  which may also result in a more precise analysis (less false alarms) than
  with the generated data dependencies.

When data dependencies are specified on a subprogram, they should mention all
global data read and written in the subprogram. When a subprogram has neither
global inputs nor global outputs, it can be specified using the ``null`` data
dependencies:

.. code-block:: ada

   function Get (X : T) return Integer with
     Global => null;

When a subprogram has only global inputs but no global outputs, it can be
specified either using the ``Input`` mode:

.. code-block:: ada

   function Get_Sum return Integer with
     Global => (Input => (X, Y, Z));

or equivalently without any mode:

.. code-block:: ada

   function Get_Sum return Integer with
     Global => (X, Y, Z);

Note the use of parentheses around a list of global inputs or outputs for a
given mode.

Global data that is both read and written should be mentioned with the
``In_Out`` mode, and not as both input and output. For example, the following
data dependencies on ``Add_To_Total`` are illegal and rejected by |GNATprove|:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Global => (Input  => Total,
                Output => Total);  --  INCORRECT

Global data that is partially written in the subprogram should also be
mentioned with the ``In_Out`` mode, and not as an output. See :ref:`Data
Initialization Policy`.

.. _Flow Dependencies:

Flow Dependencies
-----------------

[|SPARK|]

The flow dependencies of a subprogram specify how its outputs (both output
parameters and global outputs) depend on its inputs (both input parameters and
global inputs). For example, flow dependencies can be specified for procedure
``Add_To_Total`` which increments global counter ``Total`` as follows:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Depends => (Total => (Total, Incr));

The above flow dependencies can be read as "the output value of global variable
``Total`` depends on the input values of global variable ``Total`` and
parameter ``Incr``".

Flow dependencies have no impact on compilation and the run-time behavior of a
program. When a subprogram is analyzed with |GNATprove|, it checks that, in the
implementation of the subprogram, outputs depend on inputs as specified in the
flow dependencies. During its analysis, |GNATprove| uses the specified flow
dependencies of callees to analyze callers, if present, otherwise a default
flow dependency contract is generated for callees (see :ref:`Generation of
Dependency Contracts`).

When flow dependencies are specified on a subprogram, they should mention all
flows from inputs to outputs. In particular, the output value of a parameter or
global variable that is partially written by a subprogram depends on its input
value (see :ref:`Data Initialization Policy`).

When the output value of a parameter or global variable depends on its input
value, the corresponding flow dependency can use the shorthand symbol ``*`` to
denote that a variable's output value depends on the variable's input value
plus any other input listed. For example, the flow dependencies of
``Add_To_Total`` above can be specified equivalently:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Depends => (Total =>+ Incr);

When an output value depends on no input value, meaning that it is completely
(re)initialized with constants that do not depend on variables, the
corresponding flow dependency should use the ``null`` input list:

.. code-block:: ada

   procedure Init_Total with
     Depends => (Total => null);

.. _State Abstraction and Contracts:

State Abstraction and Contracts
-------------------------------

[|SPARK|]

The subprogram contracts mentioned so far always used directly global
variables. In many cases, this is not possible because the global variables are
defined in another unit and not directly visible (because they are defined in
the private part of a package specification, or in a package
implementation). The notion of abstract state in |SPARK| can be used in that
case (see :ref:`State Abstraction`) to name in contracts global data that is
not visible.

.. _State Abstraction and Dependencies:

State Abstraction and Dependencies
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Suppose the global variable ``Total`` incremented by procedure ``Add_To_Total``
is defined in the package implementation, and a procedure ``Cash_Tickets`` in a
client package calls ``Add_To_Total``. Package ``Account`` which defines
``Total`` can define an abstract state ``State`` that represents ``Total``, as
seen in :ref:`State Abstraction`, which allows using it in ``Cash_Tickets``'s
data and flow dependencies:

.. code-block:: ada

   procedure Cash_Tickets (Tickets : Ticket_Array) with
     Global  => (Output => Account.State),
     Depends => (Account.State => Tickets);

As global variable ``Total`` is not visible from clients of unit ``Account``,
it is not visible either in the visible part of ``Account``'s
specification. Hence, externally visible subprograms in ``Account`` must also
use abstract state ``State`` in their data and flow dependencies, for example:

.. code-block:: ada

   procedure Init_Total with
     Global  => (Output => State),
     Depends => (State => null);

   procedure Add_To_Total (Incr : in Integer) with
     Global  => (In_Out => State),
     Depends => (State =>+ Incr);

Then, unless they are not in |SPARK|, the implementations of ``Init_Total`` and
``Add_To_Total`` need to define refined data and flow dependencies introduced
respectively by ``Refined_Global`` and ``Refined_Depends``, which give the
precise dependencies for these subprograms in terms of concrete variables:

.. code-block:: ada

   procedure Init_Total with
     Refined_Global  => (Output => Total),
     Refined_Depends => (Total => null)
   is
   begin
      Total := 0;
   end Init_Total;

   procedure Add_To_Total (Incr : in Integer) with
     Refined_Global  => (In_Out => Total),
     Refined_Depends => (Total =>+ Incr)
   is
   begin
      Total := Total + Incr;
   end Add_To_Total;

Here, the refined dependencies are the same as the abstract ones where
``State`` has been replaced by ``Total``, but that's not always the case, in
particular when the abstract state is refined into multiple concrete variables
(see :ref:`State Abstraction`). |GNATprove| checks that:

* the concrete global inputs are a subset of the abstract global inputs
* the concrete global outputs are a subset of the abstract global outputs
* between the abstract and the concrete view, the outputs that are not also
  inputs represent exactly the same global data
* the concrete flow dependencies are a subset of the abstract flow dependencies

|GNATprove| uses the abstract contract (data and flow dependencies) of
``Init_Total`` and ``Add_To_Total`` when analyzing calls outside package
``Account`` and the more precise refined contract (refined data and flow
dependencies) of ``Init_Total`` and ``Add_To_Total`` when analyzing calls
inside package ``Account``.

.. _State Abstraction and Functional Contracts:

State Abstraction and Functional Contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If global variables are not visible for data dependencies, they are not visible
either for functional contracts. For example, in the case of procedure
``Add_To_Total``, if global variable ``Total`` is not visible, we cannot
express anymore the precondition and postcondition of ``Add_To_Total`` as in
:ref:`Preconditions` and :ref:`Postconditions`. Instead, we define accessor
functions to retrieve properties of the state that we need to express, and we
use these in contracts. For example here:

.. code-block:: ada

   function Get_Total return Integer;

   procedure Add_To_Total (Incr : in Integer) with
     Pre  => Incr >= 0 and then Get_Total in 0 .. Integer'Last - Incr,
     Post => Get_Total = Get_Total'Old + Incr;

Function ``Get_Total`` may be defined either in the private part of package
``Account`` or in its implementation. It may take the form of a regular
function or an expression function (see :ref:`Expression Functions`), for
example:

.. code-block:: ada

   Total : Integer;

   function Get_Total return Integer is (Total);

Although no refined preconditions and postconditions are required on the
implementation of ``Add_To_Total``, it is possible to provide a refined
postcondition introduced by ``Refined_Post`` in that case, which specifies a
more precise functional behavior of the subprogram. For example, procedure
``Add_To_Total`` may also increment the value of a counter ``Call_Count`` at
each call, which can be expressed in the refined postcondition:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Refined_Post => Total = Total'Old + Incr and Call_Count = Call_Count'Old + 1
   is
      ...
   end Add_To_Total;

A refined postcondition can be given on a subprogram implementation even when
the unit does not use state abstraction, and even when the default
postcondition of ``True`` is used implicitly on the subprogram declaration.

|GNATprove| uses the abstract contract (precondition and postcondition) of
``Add_To_Total`` when analyzing calls outside package ``Account`` and the more
precise refined contract (precondition and refined postcondition) of
``Add_To_Total`` when analyzing calls inside package ``Account``.

Package Contracts
=================

Subprograms are not the only entities to bear contracts in |SPARK|. Package
contracts are made up of various optional parts:

* The `state abstraction` specifies how global variables defined in the package
  are referred to abstractly where they are not visible. Aspect
  ``Abstract_State`` introduces abstract names and aspect ``Refined_State``
  specifies the mapping between these names and global variables.
* The `package initialization` introduced by aspect ``Initializes`` specifies
  which global data (global variables and abstract state) defined in the
  package is initialized at package startup.
* The `package initial condition` introduced by aspect ``Initial_Condition``
  specifies the properties holding after package startup.

Package startup (a.k.a. package `elaboration` in Ada RM) consists in the
evaluation of all declarations in the package specification and implementation,
in particular the evaluation of constant declarations and those variable
declarations which contain an initialization expression, as well as the
statements sometimes given at the end of a package body that are precisely
executed at package startup.

.. _State Abstraction:

State Abstraction
-----------------

[|SPARK|]

The state abstraction of a package specifies a mapping between abstract names
and concrete global variables defined in the package. State abstraction allows
to define :ref:`Subprogram Contracts` at an abstract level that does not depend
on a particular choice of implementation (see :ref:`State Abstraction and
Contracts`), which is better both for maintenance (no need to change contracts)
and scalability of analysis (contracts can be much smaller).

One abstract name may be mapped to more than one concrete variable, but no two
abstract names can be mapped to the same concrete variable. When state
abstraction is specified on a package, all non-visible global variables defined
in the private part of the package specification and in its implementation
should be mapped to abstract names. Thus, abstract names correspond to a
partitioning of the non-visible global variables defined in the package.

The simplest use of state abstraction is to define a single abstract name
(conventionally called ``State``) to denote all non-visible global variables
defined in the package. For example, consider package ``Account`` defining a
global variable ``Total`` in its implementation, which is abstracted as
``State``:

.. code-block:: ada

   package Account with
     Abstract_State => State
   is
      ...
   end Account;

   package body Account with
     Refined_State => (State => Total)
   is
      Total : Integer;
      ...
   end Account;

The aspect ``Refined_State`` maps each abstract name to a list of concrete
global variables defined in the package. The list can be simply ``null`` to
serve as placeholder for future definitions of global variables. Instead of
concrete global variables, one can also use abstract names for the state of
nested packages and private child packages, whose state is considered to be
also defined in the parent package.

If global variable ``Total`` is defined in the private part of ``Account``'s
package specification, then the declaration of ``Total`` must use the special
aspect ``Part_Of`` to declare its membership in abstract state ``State``:

.. code-block:: ada

   package Account with
     Abstract_State => State
   is
      ...
   private
     Total : Integer with Part_Of => State;
     ...
   end Account;

This ensures that ``Account``'s package specification can be checked by
|GNATprove| even if its implementation is not in |SPARK|, or not available for
analysis, or not yet developed.

In general, an abstract name corresponds to multiple global variables defined
in the package. For example, we can imagine adding global variables to log
values passed in argument to procedure ``Add_To_Total``, that are also mapped to
abstract name ``State``:

.. code-block:: ada

   package Account with
     Abstract_State => State
   is
      ...
   end Account;

   package body Account with
     Refined_State => (State => (Total, Log, Log_Size))
   is
      Total    : Integer;
      Log      : Integer_Array;
      Log_Size : Natural;
      ...
   end Account;

We can also imagine defining different abstract names for the total and the log:

.. code-block:: ada

   package Account with
     Abstract_State => (State, Internal_State)
   is
      ...
   end Account;

   package body Account with
     Refined_State => (State => Total,
                       Internal_State => (Log, Log_Size))
   is
      Total    : Integer;
      Log      : Integer_Array;
      Log_Size : Natural;
      ...
   end Account;

The abstract names defined in a package are visible everywhere the package name
itself is visible:

* in the scope where the package is declared, for a locally defined package
* in units that have a clause ``with <package>;``
* in units that have a clause ``limited with <package>;``

The last case allows subprograms in two packages to mutually reference the
abstract state of the other package in their data and flow dependencies.

.. _Package Initialization:

Package Initialization
----------------------

[|SPARK|]

The package initialization specifies which global data (global variables and
abstract state) defined in the package is initialized at package startup. The
corresponding global variables may either be initialized at declaration, or by
the package body statements. Thus, package initialization can be seen as the
output data dependencies of the package elaboration procedure generated by the
compiler.

For example, we can specify that the state of package ``Account`` is
initialized at package startup as follows:

.. code-block:: ada

   package Account with
     Abstract_State => State,
     Initializes    => State
   is
      ...
   end Account;

Then, unless ``Account``'s implementation is not in |SPARK|, it should
initialize the corresponding global variable ``Total`` either at declaration:

.. code-block:: ada

   package body Account with
     Refined_State => (State => Total)
   is
      Total : Integer := 0;
      ...
   end Account;

or in the package body statements:

.. code-block:: ada

   package body Account with
     Refined_State => (State => Total)
   is
      Total : Integer;
      ...
   begin
      Total := 0;
   end Account;

These initializations need not correspond to direct assignments, but may be
performed in a call, for example here to procedure ``Init_Total`` as seen in
:ref:`State Abstraction and Dependencies`. A mix of initializations at
declaration and in package body statements is also possible.

.. _Package Initial Condition:

Package Initial Condition
-------------------------

[|SPARK|]

The package initial condition specifies the properties holding after package
startup.  Thus, package initial condition can be seen as the postcondition of
the package elaboration procedure generated by the compiler.  For example, we
can specify that the value of ``Total`` defined in package ``Account``'s
implementation is initially zero:

.. code-block:: ada

   package Account with
     Abstract_State    => State,
     Initial_Condition => Get_Total = 0
   is
      function Get_Total return Integer;
      ...
   end Account;

This is ensured either by initializing ``Total`` with value zero at
declaration, or by assigning the value zero to ``Total`` in the package body
statements, as seen in :ref:`Package Initialization`.

When the program is compiled with assertions (for example with switch
``-gnata`` in |GNAT Pro|), the initial condition of a package is checked at run
time after package startup. An exception is raised if the initial condition
fails.

When a package is analyzed with |GNATprove|, it checks that the initial
condition of a package cannot fail. |GNATprove| also analyzes the initial
condition expression to ensure that it is free from run-time errors, like any
other assertion.

.. _Interfaces to the Physical World:

Interfaces to the Physical World
--------------------------------

[|SPARK|]

Volatile Variables
^^^^^^^^^^^^^^^^^^

Most embedded programs interact with the physical world or other programs
through so-called `volatile` variables, which are identified as volatile to
protect them from the usual compiler optimizations. In |SPARK|, volatile
variables are also analyzed specially, so that possible changes to their value
from outside the program are taken into account, and so that changes to their
value from inside the program are also interpreted correctly (in particular for
checking flow dependencies).

For example, consider package ``Volatile_Or_Not`` which defines a volatile
variable ``V`` and a non-volatile variable ``N``, and procedure
``Swap_Then_Zero`` which starts by swapping the values of ``V`` and ``N``
before zeroing them out:

.. literalinclude:: gnatprove_by_example/examples/volatile_or_not.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/volatile_or_not.adb
   :language: ada
   :linenos:

Compare the difference in contracts between volatile variable ``V`` and
non-volatile variable ``N``:

* The :ref:`Package Initialization` of package ``Volatile_Or_Not`` mentions
  ``V`` although this variable is not initialized at declaration or in the
  package body statements. This is because a volatile variable is assumed to be
  initialized.

* The :ref:`Flow Dependencies` of procedure ``Swap_Then_Zero`` are very
  different for ``V`` and ``N``. If both variables were not volatile, the
  correct contract would state that both input values are not used with ``null
  => (V, N)`` and that both output values depend on no inputs with ``(V, N) =>
  null``. The difference comes the special treatment of volatile variable
  ``V``: as its value may be read at any time, the intermediate value ``N``
  assigned to ``V`` on line 8 of ``volatile_or_not.adb`` needs to be mentioned
  in the flow dependencies for output ``V``.

|GNATprove| checks that ``Volatile_Or_Not`` and ``Swap_Then_Zero`` implement
their contract, and it issues a warning on the first assignment to ``N``:

.. literalinclude:: gnatprove_by_example/results/volatile_or_not.flow
   :language: none

This warning points to a real issue, as the intermediate value of ``N`` is not
used before ``N`` is zeroed out on line 12. But note that no warning is issued
on the similar first assignment to ``V``, because the intermediate value of
``V`` may be read outside the program before ``V`` is zeroed out on line 11.

Note that in real code, the memory address of the volatile variable is set
through aspect ``Address`` or the corresponding representation clause, so that
it can be read or written outside the program.

.. _Flavors of Volatile Variables:

Flavors of Volatile Variables
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Not all volatile variables are read and written outside the program, sometimes
they are only read or only written outside the program. For example, the log
introduced in :ref:`State Abstraction` could be implemented as an output port
for the program logging the information, and as an input port for the program
performing the logging. Two aspects are defined in |SPARK| to distinguish these
different flavors of volatile variables:

* Aspect ``Async_Writers`` indicates that the value of the variable may be
  changed at any time (asynchronously) by hardware or software outside the
  program.

* Aspect ``Async_Readers`` indicates that the value of the variable may be read
  at any time (asynchronously) by hardware or software outside the program.

Only ``Async_Writers`` has an effect on |GNATprove|'s analysis: during proof,
two successive reads of the same variable may return different
results. ``Async_Readers`` serves mostly a documentation purpose. In
particular, neither ``Async_Writers`` nor ``Async_Readers`` change flow
analysis. Thus, these aspects are well suited to model respectively a sensor
and a display, but not an input stream or an actuator, for which the act of
reading or writing has an effect that should be reflected in the flow
dependencies. Two more aspects are defined in |SPARK| to further refine the
previous flavors of volatile variables:

* Aspect ``Effective_Reads`` indicates that reading the value of the variable
  has an effect (for example, removing a value from an input stream). It can
  only be specified on a variable that also has ``Async_Writers`` set.

* Aspect ``Effective_Writes`` indicates that writing the value of the variable
  has an effect (for example, sending a command to an actuator). It can only be
  specified on a variable that also has ``Async_Readers`` set.

Both aspects ``Effective_Reads`` and ``Effective_Writes`` have an effect on
|GNATprove|'s flow analysis: reading the former or writing the latter is
modelled as having an effect on the value of the variable, which needs to be
reflected in flow dependencies. Because reading a variable with
``Effective_Reads`` set has an effect on its value, such a variable cannot be
only a subprogram input, it must be also an output.

For example, the program writing in a log each value passed as argument to
procedure ``Add_To_Total`` may model the output port ``Log_Out`` as a volatile
variable with ``Async_Readers`` and ``Effective_Writes`` set:

.. literalinclude:: gnatprove_by_example/examples/logging_out.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/logging_out.adb
   :language: ada
   :linenos:

while the logging program may model the input port ``Log_In`` as a volatile
variable with ``Async_Writers`` and ``Effective_Reads`` set:

.. literalinclude:: gnatprove_by_example/examples/logging_in.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/logging_in.adb
   :language: ada
   :linenos:

|GNATprove| checks the specified data and flow dependencies on both programs.

A volatile variable on which none of the four aspects ``Async_Writers``,
``Async_Readers``, ``Effective_Reads`` or ``Effective_Writes`` is set is
assumed to have all four aspects set to ``True``. A volatile variable on which
some of the four aspects are set to ``True`` is assumed to have the remaining
ones set to ``False``. See SPARK RM 7.1.3 for details.

External State Abstraction
^^^^^^^^^^^^^^^^^^^^^^^^^^

Volatile variables may be part of :ref:`State Abstraction`, in which case the
volatility of the abstract name must be specified by using aspect ``External``
on the abstract name, as follows:

.. code-block:: ada

   package Account with
     Abstract_State => (State with External)
   is
      ...
   end Account;

An external state may represent both volatile variables and non-volatile ones,
for example:

.. code-block:: ada

   package body Account with
     Refined_State => (State => (Total, Log, Log_Size))
   is
      Total    : Integer;
      Log      : Integer_Array with Volatile;
      Log_Size : Natural with Volatile;
      ...
   end Account;

The different :ref:`Flavors of Volatile Variables` may also be specified in the
state abstraction, which is then used by |GNATprove| to refine the
analysis. For example, the program writing in a log seen in the previous
section can be rewritten to abstract global variables as follows:

.. literalinclude:: gnatprove_by_example/examples/logging_out_abstract.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/logging_out_abstract.adb
   :language: ada
   :linenos:

while the logging program seen in the previous section may be rewritten to
abstract global variables as follows:

.. literalinclude:: gnatprove_by_example/examples/logging_in_abstract.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/logging_in_abstract.adb
   :language: ada
   :linenos:

|GNATprove| checks the specified data and flow dependencies on both programs.

An external abstract state on which none of the four aspects ``Async_Writers``,
``Async_Readers``, ``Effective_Reads`` or ``Effective_Writes`` is set is
assumed to have all four aspects set to ``True``. An external abstract state on
which some of the four aspects are set to ``True`` is assumed to have the
remaining ones set to ``False``. See SPARK RM 7.1.2 for details.

Type Contracts
==============

|SPARK| contains various features to constrain the values of a given type:

* A *scalar range* may be specified on a scalar type or subtype to bound its
  values.
* A *static predicate* introduced by aspect ``Static_Predicate`` may be
  specified on a scalar type or subtype to list values allowed or forbidden.
* A *record discriminant* may be specified on a record type to distinguish
  between variants of the same record.
* A *default initial condition* introduced by aspect
  ``Default_Initial_Condition`` on a private type specifies the initialization
  status and possibly properties of the default initialization for a type.

Note that |SPARK| does not yet support aspects ``Dynamic_Predicate`` and
``Type_Invariant`` from Ada 2012.

.. _Scalar Ranges:

Scalar Ranges
-------------

[Ada 83]

Scalar types (signed integer types, modulo types, fixed-point types,
floating-point types) can be given a low bound and a high bound to specify that
values of the type must remain within these bounds. For example, the global
counter ``Total`` can never be negative, which can be expressed in its type:

.. code-block:: ada

   Total : Integer range 0 .. Integer'Last;

Any attempt to assign a negative value to variable ``Total`` results in raising
an exception at run time. During analysis, |GNATprove| checks that all values
assigned to ``Total`` are positive or null. The anonymous subtype above can
also be given an explicit name:

.. code-block:: ada

   subtype Nat is Integer range 0 .. Integer'Last;
   Total : Nat;

or we can use the equivalent standard subtype ``Natural``:

.. code-block:: ada

   Total : Natural;

or ``Nat`` can be defined as a derived type instead of a subtype:

.. code-block:: ada

   type Nat is new Integer range 0 .. Integer'Last;
   Total : Nat;

or as a new signed integer type:

.. code-block:: ada

   type Nat is range 0 .. Integer'Last;
   Total : Nat;

All the variants above result in the same range checks both at run-time and in
|GNATprove|. |GNATprove| also uses the range information for proving properties
about the program (for example, the absence of overflows in computations).

Static Predicates
-----------------

[Ada 2012]

A static predicate allows specifying which values are allowed or forbidden in a
scalar type, when this specification cannot be expressed with :ref:`Scalar
Ranges` (because it has *holes*). For example, we can express that the global
counter ``Total`` cannot be equal to ``10`` or ``100`` with the following
static predicate:

.. code-block:: ada

   subtype Count is Integer with
     Static_Predicate => Count /= 10 and Count /= 100;
   Total : Count;

or equivalently:

.. code-block:: ada

   subtype Count is Integer with
     Static_Predicate => Count in Integer'First .. 9 | 11 .. 99 | 101 .. Integer'Last;
   Total : Count;

Uses of the name of the subtype ``Count`` in the predicate refer to variables
of this type. Scalar ranges and static predicates can also be combined, and
static predicates can be specified on subtypes, derived types and new signed
integer types. For example, we may define ``Count`` as follows:

.. code-block:: ada

   type Count is new Natural with
     Static_Predicate => Count /= 10 and Count /= 100;

Any attempt to assign a forbidden value to variable ``Total`` results in
raising an exception at run time. During analysis, |GNATprove| checks that all
values assigned to ``Total`` are allowed. |GNATprove| also uses the predicate
information for proving properties about the program.

Record Discriminants
---------------------

[Ada 83]

Record types can use discriminants to:

* define multiple variants and associate each component to a specific variant
* bound the size of array components

For example, the log introduced in :ref:`State Abstraction` could be
implemented as a discriminated record with a discriminant ``Kind`` selecting
between two variants of the record for logging either only the minimum and
maximum entries or the last entries, and a discriminant ``Capacity`` specifying
the maximum number of entries logged:

.. literalinclude:: gnatprove_by_example/examples/logging_discr.ads
   :language: ada
   :linenos:

Subtypes of ``Log_Type`` can specify fixed values for ``Kind`` and
``Capacity``, like in ``Min_Max_Log`` and ``Ten_Values_Log``. The discriminants
``Kind`` and ``Capacity`` are accessed like regular components, for example:

.. literalinclude:: gnatprove_by_example/examples/logging_discr.adb
   :language: ada
   :linenos:

Any attempt to access a component not present in a variable (because it is of a
different variant), or to access an array component outside its bounds, results
in raising an exception at run time. During analysis, |GNATprove| checks that
components accessed are present, and that array components are accessed within
bounds:

.. literalinclude:: gnatprove_by_example/results/logging_discr.prove
   :language: none

Default Initial Condition
-------------------------

[|SPARK|]

Private types in a package define an encapsulation mechanism that prevents
client units from accessing the implementation of the type. That boundary may
also be used to specify properties that hold for default initialized values of
that type in client units. For example, the log introduced in :ref:`State
Abstraction` could be implemented as a private type with a default initial
condition specifying that the size of the log is initially zero, where uses of
the name of the private type ``Log_Type`` in the argument refer to variables of
this type:

.. literalinclude:: gnatprove_by_example/examples/logging_priv.ads
   :language: ada
   :linenos:

This may be useful to analyze with |GNATprove| client code that defines a
variable of type ``Log_Type`` with default initialization, and then proceeds to
append values to this log, as procedure ``Append_To_Log``'s precondition
requires that the log size is not maximal:

.. code-block:: ada

   The_Log : Log_Type;
   ...
   Append_To_Log (The_Log, X);

|GNATprove|'s flow analysis also uses the presence of a default initial
condition as an indication that default initialized variables of that type are
considered as fully initialized. So the code snippet above would pass flow
analysis without messages being issued on the read of ``The_Log``. If the full
definition of the private type is in |SPARK|, |GNATprove| also checks that the
type is indeed fully default initialized, and if not issues a message like
here:

.. literalinclude:: gnatprove_by_example/results/logging_priv.flow
   :language: none

If partial default initialization of the type is intended, in general for
efficiency like here, then the corresponding message can be justified with
pragma ``Annotate``, see section :ref:`Justifying Check Messages`.

Aspect ``Default_Initial_Condition`` can also be specified without argument to
only indicate that default initialized variables of that type are considered as
fully initialized. This is equivalent to ``Default_Initial_Condition => True``:

.. code-block:: ada

   type Log_Type is private with
     Default_Initial_Condition;

The argument can also be ``null`` to specify that default initialized variables
of that type are *not* considered as fully initialized:

.. code-block:: ada

   type Log_Type is private with
     Default_Initial_Condition => null;

This is different from an argument of ``False`` which can be used to indicate
that variables of that type should always be explicitly initialized (otherwise
|GNATprove| will not be able to prove the condition ``False`` on the default
initialization and will issue a message during proof).

Specification Features
======================

|SPARK| contains many features for specifying the intended behavior of
programs. Some of these features come from Ada 2012 (:ref:`Attribute Old` and
:ref:`Expression Functions` for example). Other features are specific to
|SPARK| (:ref:`Attribute loop_Entry` and :ref:`Ghost Code` for example). In
this section, we describe these features and their impact on execution and
formal verification.

.. _Attribute Old:

Attribute ``Old``
-----------------

[Ada 2012]

In a Postcondition
^^^^^^^^^^^^^^^^^^

Inside :ref:`Postconditions`, attribute ``Old`` refers to the values that
expressions had at subprogram entry. For example, the postcondition of
procedure ``Increment`` might specify that the value of parameter ``X`` upon
returning from the procedure has been incremented:

.. code-block:: ada

   procedure Increment (X : in out Integer) with
     Post => X = X'Old + 1;

At run time, a copy of the variable ``X`` is made when entering the
subprogram. This copy is then read when evaluating the expression ``X'Old`` in
the postcondition. Because it requires copying the value of ``X``, the type of
``X`` cannot be limited.

Strictly speaking, attribute ``Old`` must apply to a *name* in Ada syntax, for
example a variable, a component selection, a call, but not an addition like
``X + Y``. For expressions that are not *names*, attribute ``Old`` can be applied
to their qualified version, for example:

.. code-block:: ada

   procedure Increment_One_Of (X, Y : in out Integer) with
     Post => X + Y = Integer'(X + Y)'Old + 1;

Because the compiler unconditionnally creates a copy of the expression to which
attribute ``Old`` is applied at subprogram entry, there is a risk that this feature
might confuse users in more complex postconditions. Take the example of a
procedure ``Extract``, which copies the value of array ``A`` at index ``J`` into
parameter ``V``, and zeroes out this value in the array, but only if ``J`` is
in the bounds of ``A``:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Post => (if J in A'Range then V = A(J)'Old);  --  INCORRECT

Clearly, the value of ``A(J)`` at subprogram entry is only meaningful if ``J``
is in the bounds of ``A``. If the code above was allowed, then a copy of
``A(J)`` would be made on entry to subprogram ``Extract``, even when ``J`` is
out of bounds, which would raise a run-time error. To avoid this common
pitfall, use of attribute ``Old`` in expressions that are potentially unevaluated
(like the then-part in an if-expression, or the right argument of a shortcut
boolean expression - See Ada RM 6.1.1) is restricted to
plain variables: ``A`` is allowed, but not ``A(J)``. The |GNAT Pro| compiler
issues the following error on the code above::

   prefix of attribute "Old" that is potentially unevaluated must denote an entity

The correct way to specify the postcondition in the case above is to apply
attribute ``Old`` to the entity prefix ``A``:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Post => (if J in A'Range then V = A'Old(J));

In Contract Cases
^^^^^^^^^^^^^^^^^

The rule for attribute ``Old`` inside :ref:`Contract Cases` is more
permissive. Take for example the same contract as above for procedure
``Extract``, expressed with contract cases:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Contract_Cases => ((J in A'Range) => V = A(J)'Old,
                        others         => True);

Only the expressions used as prefixes of attribute ``Old`` in the *currently
enabled case* are copied on entry to the subprogram. So if ``Extract`` is
called with ``J`` out of the range of ``A``, then the second case is enabled,
so ``A(J)`` is not copied when entering procedure ``Extract``. Hence, the above
code is allowed.

It may still be the case that some contracts refer to the value of objects at
subprogram entry inside potentially unevaluated expressions. For example, an
incorrect variation of the above contract would be:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Contract_Cases => (J >= A'First => (if J <= A'Last then V = A(J)'Old),  --  INCORRECT
                        others       => True);

For the same reason that such uses are forbidden by Ada RM inside
postconditions, the SPARK RM forbids these uses inside contract cases (see
SPARK RM 6.1.3(2)). The |GNAT Pro| compiler issues the following error on the code
above::

   prefix of attribute "Old" that is potentially unevaluated must denote an entity

The correct way to specify the consequence expression in the case above is to
apply attribute ``Old`` to the entity prefix ``A``:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Contract_Cases => (J >= A'First => (if J <= A'Last then V = A'Old(J)),
                        others       => True);

.. _In a Potentially Unevaluated Expression:

In a Potentially Unevaluated Expression
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In some cases, the compiler issues the error discussed above (on attribute ``Old``
applied to a non-entity in a potentially unevaluated context) on an expression
that can safely be evaluated on subprogram entry, for example:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Post => (if J in A'Range then V = Get_If_In_Range(A,J)'Old);  --  ERROR

where function ``Get_If_In_Range`` returns the value ``A(J)`` when ``J`` is in
the bounds of ``A``, and a default value otherwise.

In that case, the solution is either to rewrite the postcondition using
non-shortcut boolean operators, so that the expression is not *potentially
evaluated* anymore, for example:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Post => J not in A'Range or V = Get_If_In_Range(A,J)'Old;

or to use the |GNAT Pro| pragma ``Unevaluated_Use_Of_Old`` to allow such uses
of attribute ``Old`` in potentially unevaluated expressions:

.. code-block:: ada

   pragma Unevaluated_Use_Of_Old (Allow);

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Post => (if J in A'Range then V = Get_If_In_Range(A,J)'Old);

|GNAT Pro| does not issue an error on the code above, and always evaluates the
call to ``Get_If_In_Range`` on entry to procedure ``Extract``, even if this
value may not be used when executing the postcondition. Note that the formal
verification tool |GNATprove| correctly generates all required checks to prove
that this evaluation on subprogram entry does not fail a run-time check or a
contract (like the precondition of ``Get_If_In_Range`` if any).

Pragma ``Unevaluated_Use_Of_Old`` applies to uses of attribute ``Old`` both
inside postconditions and inside contract cases. See |GNAT Pro| RM for a
detailed description of this pragma.

.. _Attribute Result:

Attribute ``Result``
--------------------

[Ada 2012]

Inside :ref:`Postconditions` of functions, attribute ``Result`` refers to the
value returned by the function. For example, the postcondition of function
``Increment`` might specify that it returns the value of parameter ``X`` plus
one:

.. code-block:: ada

   function Increment (X : Integer) return Integer with
     Post => Increment'Result = X + 1;

Contrary to ``Attribute Old``, attribute ``Result`` does not require copying
the value, hence it can be applied to functions that return a limited
type. Attribute ``Result`` can also be used inside consequence expressions in
:ref:`Contract Cases`.

.. _Attribute Loop_Entry:

Attribute ``Loop_Entry``
------------------------

[|SPARK|]

It is sometimes convenient to refer to the value of variables at loop entry. In
many cases, the variable has not been modified between the subprogram entry and
the start of the loop, so this value is the same as the value at subprogram
entry. But :ref:`Attribute Old` cannot be used in that case. Instead, we can
use attribute ``Loop_Entry``. For example, we can express that after ``J``
iterations of the loop, the value of parameter array ``X`` at index ``J`` is
equal to its value at loop entry plus one:

.. code-block:: ada

   procedure Increment_Array (X : in out Integer_Array) is
   begin
      for J in X'Range loop
         X(J) := X(J) + 1;
         pragma Assert (X(J) = X'Loop_Entry(J) + 1);
      end loop
   end Increment_Array;

At run time, a copy of the variable ``X`` is made when entering the loop. This
copy is then read when evaluating the expression ``X'Loop_Entry``. No copy is
made if the loop is never entered. Because it requires copying the value of
``X``, the type of ``X`` cannot be limited.

Attribute ``Loop_Entry`` can only be used in top-level :ref:`Assertion Pragmas`
inside a loop. It is mostly useful for expressing complex :ref:`Loop
Invariants` which relate the value of a variable at a given iteration of the
loop and its value at loop entry. For example, we can express that after ``J``
iterations of the loop, the value of parameter array ``X`` at all indexes
already seen is equal to its value at loop entry plus one, using
:ref:`Quantified Expressions`:

.. code-block:: ada

   procedure Increment_Array (X : in out Integer_Array) is
   begin
      for J in X'Range loop
         X(J) := X(J) + 1;
         pragma Loop_Invariant (for all K in X'First .. J => X(J) = X'Loop_Entry(J) + 1);
      end loop
   end Increment_Array;

Attribute ``Loop_Entry`` may be indexed by the name of the loop to which it
applies, which is useful to refer to the value of a variable on entry to an
outter loop. When used without loop name, the attribute applies to the closest
enclosing loop. For examples, ``X'Loop_Entry`` is the same as
``X'Loop_Entry(Inner)`` in the loop below, which is not the same as
``X'Loop_Entry(Outter)`` (although all three assertions are true):

.. code-block:: ada

   procedure Increment_Matrix (X : in out Integer_Matrix) is
   begin
      Outter: for J in X'Range(1) loop
         Inner: for K in X'Range(2) loop
            X(J,K) := X(J,K) + 1;
            pragma Assert (X(J) = X'Loop_Entry(J,K) + 1);
            pragma Assert (X(J) = X'Loop_Entry(Inner)(J,K) + 1);
            pragma Assert (X(J) = X'Loop_Entry(Outter)(J,K) + 1);
         end loop Inner;
      end loop Outter;
   end Increment_Matrix;

By default, similar restrictions exist for the use of attribute ``Loop_Entry``
and the use of attribute ``Old`` :ref:`In a Potentially Unevaluated
Expression`. The same solutions apply here, in particular the use of |GNAT Pro|
pragma ``Unevaluated_Use_Of_Old``.

.. _Attribute Update:

Attribute ``Update``
--------------------

[|SPARK|]

It is quite common in :ref:`Postconditions` to relate the input and output
values of parameters. While this can be as easy as ``X = X'Old + 1`` in the
case of scalar parameters, it is more complex to express for array and record
parameters. Attribute ``Update`` is useful in that case, to denote the updated
value of a composite variable. For example, we can express more clearly that
procedure ``Zero_Range`` zeroes out the elements of its array parameter ``X``
between ``From`` and ``To`` by using attribute ``Update``:

.. code-block:: ada

   procedure Zero_Range (X : in out Integer_Array; From, To : Positive) with
     Post => X = X'Old'Update(From .. To => 0);

than with an equivalent postcondition using :ref:`Quantified Expressions` and
:ref:`Conditional Expressions`:

.. code-block:: ada

   procedure Zero_Range (X : in out Integer_Array; From, To : Positive) with
     Post => (for all J in X'Range =>
                (if J in From .. To then X(J) = 0 else X(J) = X'Old(J)));

Attribute ``Update`` takes in argument a list of associations between indexes
(for arrays) or components (for records) and values. Components can only be
mentioned once, with the semantics that all values are evaluated before any
update. Array indexes may be mentioned more than once, with the semantics that
updates are applied in left-to-right order. For example, the postcondition of
procedure ``Swap`` expresses that the values at indexes ``J`` and ``K`` in
array ``X`` have been swapped:

.. code-block:: ada

   procedure Swap (X : in out Integer_Array; J, K : Positive) with
     Post => X = X'Old'Update(J => X'Old(K), K => X'Old(J));

and the postcondition of procedure ``Rotate_Clockwize_Z`` expresses that the
point ``P`` given in parameter has been rotated 90 degrees clockwise around the
Z axis (thus component ``Z`` is preserved while components ``X`` and ``Y`` are
modified):

.. code-block:: ada

   procedure Rotate_Clockwize_Z (P : in out Point_3D) with
     Post => P = P'Old'Update(X => P.Y'Old, Y => - P.X'Old);

Similarly to its use in combination with attribute ``Old`` in postconditions,
attribute ``Update`` is useful in combination with :ref:`Attribute Loop_Entry`
inside :ref:`Loop Invariants`. For example, we can express the property that,
after iteration ``J`` in the main loop in procedure ``Zero_Range``, the value
of parameter array ``X`` at all indexes already seen is equal to zero:

.. code-block:: ada

   procedure Zero_Range (X : in out Integer_Array; From, To : Positive) is
   begin
      for J in From .. To loop
         X(J) := 0;
         pragma Loop_Invariant (X = X'Loop_Entry'Update(From .. J => 0));
      end loop;
   end Zero_Range;

Attribute ``Update`` can also be used outside of assertions. It is particularly
useful in expression functions. For example, the functionality in procedure
``Rotate_Clockwize_Z`` could be expressed equivalently as an expression
function:

.. code-block:: ada

   function Rotate_Clockwize_Z (P : Point_3D) return Point_3D is
     (P'Update(X => P.Y, Y => - P.X));

Because it requires copying the value of ``P``, the type of ``P`` cannot be
limited.

.. _Conditional Expressions:

Conditional Expressions
-----------------------

[Ada 2012]

A conditional expression is a way to express alternative possibilities in an
expression. It is like the ternary conditional expression ``cond ? expr1 :
expr2`` in C or Java, except more powerful. There are two kinds of conditional
expressions in Ada:

* if-expressions are the counterpart of if-statements in expressions
* case-expressions are the counterpart of case-statements in expressions

For example, consider the variant of procedure ``Add_To_Total`` seen in
:ref:`Contract Cases`, which saturates at a given threshold. Its postcondition
can be expressed with an if-expression as follows:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => (if Total'Old + Incr < Threshold  then
                Total = Total'Old + Incr
              else
                Total = Threshold);

Each branch of an if-expression (there may be one, two or more branches when
``elsif`` is used) can be seen as a logical implication, which explains why the
above postcondition can also be written:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => (if Total'Old + Incr < Threshold then Total = Total'Old + Incr) and
             (if Total'Old + Incr >= Threshold then Total = Threshold);

or equivalently (as the absence of ``else`` branch above is implicitly the same
as ``else True``):

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => (if Total'Old + Incr < Threshold then Total = Total'Old + Incr else True) and
             (if Total'Old + Incr >= Threshold then Total = Threshold else True);

If-expressions are not necessarily of boolean type, in which case they must
have an ``else`` branch that gives the value of the expression for cases not
covered in previous conditions (as there is no implicit ``else True`` in such
a case). For example, here is a postcondition equivalent to the above, that
uses an if-expression of ``Integer`` type:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => Total = (if Total'Old + Incr < Threshold then Total'Old + Incr else Threshold);

Although case-expressions can be used to cover cases of any scalar type, they
are mostly used with enumerations, and the compiler checks that all cases are
disjoint and that together they cover all possible cases. For example, consider
a variant of procedure ``Add_To_Total`` which takes an additional ``Mode``
global input of enumeration value ``Single``, ``Double``, ``Negate`` or
``Ignore``, with the intuitive corresponding leverage effect on the
addition. The postcondition of this variant can be expressed using a
case-expression as follows:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => (case Mode is
                when Single => Total = Total'Old + Incr,
                when Double => Total = Total'Old + 2 * Incr,
                when Ignore => Total = Total'Old,
                when Negate => Total = Total'Old - Incr);

Like if-expressions, case-expressions are not necessarily of boolean type. For
example, here is a postcondition equivalent to the above, that uses a
case-expression of ``Integer`` type:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => Total = Total'Old + (case Mode is
                                    when Single => Incr,
                                    when Double => 2 * Incr,
                                    when Ignore => 0,
                                    when Negate => - Incr);

A last case of ``others`` can be used to denote all cases not covered by
previous conditions. If-expressions and case-expressions should always be
parenthesized.

.. _Quantified Expressions:

Quantified Expressions
----------------------

[Ada 2012]

A quantified expression is a way to express a property over a collection,
either an array or a container (see :ref:`Formal Containers Library`):

* a `universally quantified expression` using ``for all`` expresses a property
  that holds for all elements of a collection
* an `existentially quantified expression` using ``for some`` expresses a
  property that holds for at least one element of a collection

For example, consider the procedure ``Increment_Array`` that increments each
element of its array parameter ``X`` by one. Its postcondition can be expressed
using a universally quantified expression as follows:

.. code-block:: ada

   procedure Increment_Array (X : in out Integer_Array) with
     Post => (for all J in X'Range => X(J) = X'Old(J) + 1);

The negation of a universal property being an existential property (the
opposite is true too), the postcondition above can be expressed also using an
existentially quantified expression as follows:

.. code-block:: ada

   procedure Increment_Array (X : in out Integer_Array) with
     Post => not (for some J in X'Range => X(J) /= X'Old(J) + 1);

At run time, a quantified expression is executed like a loop, which exits as
soon as the value of the expression is known: if the property does not hold
(resp. holds) for a given element of a universally (resp. existentially)
quantified expression, execution of the loop does not proceed with remaining
elements and returns the value ``False`` (resp. ``True``) for the expression.

When a quantified expression is analyzed with |GNATprove|, it uses the logical
counterpart of the quantified expression. |GNATprove| also checks that the
expression is free from run-time errors. For this checking, |GNATprove| checks
that the enclosed expression is free from run-time errors over the *entire
range* of the quantification, not only at points that would actually be reached
at run time. As an example, consider the following expression:

.. code-block:: ada

    (for all I in 1 .. 10 => 1 / (I - 3) > 0)

This quantified expression cannot raise a run-time error, because the enclosed
expression ``1 / (I - 3) > 0`` is false for the first value of the range ``I =
1``, so the execution of the loop exits immediately with the value ``False``
for the quantified expression. |GNATprove| is stricter and requires the
enclosed expression ``1 / (I - 3) > 0`` to be free from run-time errors over
the entire range ``I in 1 .. 10`` (including ``I = 3``) so it issues a check
message for a possible division by zero in this case.

Quantified expressions should always be parenthesized.

.. _Expression Functions:

Expression Functions
--------------------

[Ada 2012]

An expression function is a function whose implementation is given by a single
expression. For example, the function ``Increment`` can be defined as an
expression function as follows:

.. code-block:: ada

   function Increment (X : Integer) return Integer is (X + 1);

For compilation and execution, this definition is equivalent to:

.. code-block:: ada

   function Increment (X : Integer) return Integer is
   begin
      return X + 1;
   end Increment;

For |GNATprove|, this definition as expression function is equivalent to the
same function body as above, plus a postcondition:

.. code-block:: ada

   function Increment (X : Integer) return Integer with
     Post => Increment'Result = X + 1
   is
   begin
      return X + 1;
   end Increment;

Thus, a user does not need in general to add a postcondition to an expression
function, as the implicit postcondition generated by |GNATprove| is the most
precise one. If a user adds a postcondition to an expression function,
|GNATprove| uses this postcondition to analyze the function's callers instead
of the most precise implicit postcondition. For example, we can choose to hide
the exact implementation of ``Increment`` to analyze its callers, and rely
instead for these analyses on the fact that ``Increment``'s result is greater
than its parameter:

.. code-block:: ada

   function Increment (X : Integer) return Integer is (X + 1) with
     Post => Increment'Result > X;

On the contrary, it may be useful in general to add a precondition to an
expression function, to constrain the contexts in which it can be called. For
example, parameter ``X`` passed to function ``Increment`` should be less than
the maximal integer value, otherwise an overflow would occur. We can specify
this property in ``Increment``'s precondition as follows:

.. code-block:: ada

   function Increment (X : Integer) return Integer is (X + 1) with
     Pre => X < Integer'Last;

Note that the contract of an expression function follows its expression.

Expression functions can be defined in package declarations, hence they are
well suited for factoring out common properties that are referred to in
contracts. For example, consider the procedure ``Increment_Array`` that
increments each element of its array parameter ``X`` by one. Its precondition
can be expressed using expression functions as follows:

.. code-block:: ada

   package Increment_Utils is

      function Not_Max (X : Integer) return Boolean is (X < Integer'Last);

      function None_Max (X : Integer_Array) return Boolean is
        (for all J in X'Range => Not_Max (X(J)));

      procedure Increment_Array (X : in out Integer_Array) with
        Pre => None_Max (X);

   end Increment_Utils;

Expression functions can be defined over private types, and still be used in
the contracts of publicly visible subprograms of the package, by declaring the
function publicly and defining it in the private part. For example:

.. code-block:: ada

   package Increment_Utils is

      type Integer_Array is private;

      function None_Max (X : Integer_Array) return Boolean;

      procedure Increment_Array (X : in out Integer_Array) with
        Pre => None_Max (X);

   private

      type Integer_Array is array (Positive range <>) of Integer;

      function Not_Max (X : Integer) return Boolean is (X < Integer'Last);

      function None_Max (X : Integer_Array) return Boolean is
        (for all J in X'Range => Not_Max (X(J)));

   end Increment_Utils;

.. _Ghost Code:

Ghost Code
----------

[|SPARK|]

Sometimes, the variables and functions that are present in a program are not
sufficient to specify intended properties and to verify these properties with
|GNATprove|. In such a case, it is possible in |SPARK| to insert in the program
additional code useful for specification and verification, specially identified
with the aspect ``Ghost`` so that it can be discarded during
compilation. So-called `ghost code` in |SPARK| are these parts of the code that
are only meant for specification and verification, and have no effect on the
functional behavior of the program.

Various kinds of ghost code are useful in different situations:

* `Ghost functions` are typically used to express properties used in contracts.
* `Global ghost variables` are typically used to keep track of the current
  state of a program, or to maintain a log of past events of some type. This
  information can then be referred to in contracts.
* `Local ghost variables` are typically used to hold intermediate values during
  computation, which can then be referred to in assertion pragmas like loop
  invariants.
* `Ghost types` are those types only useful for defining ghost variables.
* `Ghost procedures` can be used to factor out common treatments on ghost
  variables. Ghost procedures should not have non-ghost outputs, either output
  parameters or global outputs.
* `Ghost packages` provide a means to encapsulate all types and operations for
  a specific kind of ghost code.
* `Imported ghost subprograms` are used to provide placeholders for properties
  that are defined in a logical language, when using manual proof.

When the program is compiled with assertions (for example with switch
``-gnata`` in |GNAT Pro|), ghost code is executed like normal code. Ghost code
can also be selectively enabled by setting pragma ``Assertion_Policy`` as
follows:

.. code-block:: ada

   pragma Assertion_Policy (Ghost => Check);

|GNATprove| checks that ghost code cannot have an effect on the behavior of the
program. |GNAT Pro| compiler also performs some of these checks, although not
all of them. Apart from these checks, |GNATprove| treats ghost code like normal
code during its analyses.

.. _Ghost Functions:

Ghost Functions
^^^^^^^^^^^^^^^

Ghost functions are useful to express properties only used in contracts, and to
factor out common expressions used in contracts. For example, function
``Get_Total`` introduced in :ref:`State Abstraction and Functional Contracts`
to retrieve the value of variable ``Total`` in the contract of ``Add_To_Total``
could be marked as a ghost function as follows:

.. code-block:: ada

   function Get_Total return Integer with Ghost;

and still be used exactly as seen in :ref:`State Abstraction and Functional
Contracts`:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Pre  => Incr >= 0 and then Get_Total in 0 .. Integer'Last - Incr,
     Post => Get_Total = Get_Total'Old + Incr;

The definition of ``Get_Total`` would be also the same:

.. code-block:: ada

   Total : Integer;

   function Get_Total return Integer is (Total);

Although it is more common to define ghost functions as :ref:`Expression
Functions`, a regular function might be used too:

.. code-block:: ada

   function Get_Total return Integer is
   begin
      return Total;
   end Get_Total;

In that case, |GNATprove| uses only the contract of ``Get_Total`` (either
user-specified or the default one) when analyzing its callers, like for a
non-ghost regular function. (The same exception applies as for regular
functions, when |GNATprove| can analyze a subprogram in the context of its
callers, as described in :ref:`Contextual Analysis of Subprograms Without
Contracts`.)

In the usual context where ghost code is not kept in the final executable, the
user is given more freedom to use in ghost code constructs that are less
efficient than in normal code, which may be useful to express rich
properties. For example, the ghost functions defined in the :ref:`Formal
Containers Library` in |GNAT Pro| typically copy the entire content of the
argument container, which would not be acceptable for non-ghost functions.

Ghost Variables
^^^^^^^^^^^^^^^

Ghost variables are useful to keep track of local or global information during
the computation, which can then be referred to in contracts or assertion
pragmas.

Case 1: Keeping Intermediate Values
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Local ghost variables are commonly used to keep intermediate values. For
example, we can define a local ghost variable ``Init_Total`` to hold the
initial value of variable ``Total`` in procedure ``Add_To_Total``, which allows
checking the relation between the initial and final values of ``Total`` in an
assertion:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) is
      Init_Total : Integer := Total with Ghost;
   begin
      Total := Total + Incr;
      pragma Assert (Total = Init_Total + Incr);
   end Add_To_Total;

Case 2: Keeping Memory of Previous State
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Global ghost variables are commonly used to memorize the value of a previous
state. For example, we can define a global ghost variable ``Last_Incr`` to hold
the previous value passed in argument when calling procedure ``Add_To_Total``,
which allows checking in its precondition that the sequence of values passed in
argument is non-decreasing:

.. code-block:: ada

   Last_Incr : Integer := Integer'First with Ghost;

   procedure Add_To_Total (Incr : in Integer) with
     Pre => Incr >= Last_Incr;

   procedure Add_To_Total (Incr : in Integer) is
   begin
      Total := Total + Incr;
      Last_Incr := Incr;
   end Add_To_Total;

Case 3: Logging Previous Events
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Going beyond the previous case, global ghost variables can be used to store a
complete log of events. For example, we can define global ghost variables
``Log`` and ``Log_Size`` to hold the sequence of values passed in argument to
procedure ``Add_To_Total``, as in :ref:`State Abstraction`:

.. code-block:: ada

   Log      : Integer_Array with Ghost;
   Log_Size : Natural with Ghost;

   procedure Add_To_Total (Incr : in Integer) with
     Post => Log_Size = Log_Size'Old + 1 and Log = Log'Old'Update (Log_Size => Incr);

   procedure Add_To_Total (Incr : in Integer) is
   begin
      Total := Total + Incr;
      Log_Size := Log_Size + 1;
      Log (Log_Size) := Incr;
   end Add_To_Total;

The postcondition of ``Add_To_Total`` above expresses that ``Log_Size`` is
incremented by one at each call, and that the current value of parameter
``Incr`` is appended to ``Log`` at each call (using :ref:`Attribute Old` and
:ref:`Attribute Update`).

.. _Ghost Types:

Ghost Types
^^^^^^^^^^^

Ghost types can only be used to define ghost variables. For example, we can
define ghost types ``Log_Type`` and ``Log_Size_Type`` that specialize the types
``Integer_Array`` and ``Natural`` for ghost variables:

.. code-block:: ada

   subtype Log_Type is Integer_Array with Ghost;
   subtype Log_Size_Type is Natural with Ghost;

   Log      : Log_Type with Ghost;
   Log_Size : Log_Size_Type with Ghost;

Ghost Procedures
^^^^^^^^^^^^^^^^

Ghost procedures are useful to factor out common treatments on ghost
variables. For example, we can define a ghost procedure ``Append_To_Log`` to
append a value to the log as seen previously.

.. code-block:: ada

   Log      : Integer_Array with Ghost;
   Log_Size : Natural with Ghost;

   procedure Append_To_Log (Incr : in Integer) with
     Ghost,
     Post => Log_Size = Log_Size'Old + 1 and Log = Log'Old'Update (Log_Size => Incr);

   procedure Append_To_Log (Incr : in Integer) is
   begin
      Log_Size := Log_Size + 1;
      Log (Log_Size) := Incr;
   end Append_To_Log;

Then, this procedure can be called in ``Add_To_Total`` as follows:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) is
   begin
      Total := Total + Incr;
      Append_To_Log (Incr);
   end Add_To_Total;

.. _Ghost Packages:

Ghost Packages
^^^^^^^^^^^^^^

Ghost packages are useful to encapsulate all types and operations for a
specific kind of ghost code. For example, we can define a ghost package
``Logging`` to deal with all all logging operations on package ``Account``:

.. code-block:: ada

   package Logging with
     Ghost
   is
      Log      : Integer_Array;
      Log_Size : Natural;

      procedure Append_To_Log (Incr : in Integer) with
        Post => Log_Size = Log_Size'Old + 1 and Log = Log'Old'Update (Log_Size => Incr);

      ...

   end Logging;

The implementation of package ``Logging`` is the same as if it was not a ghost
package. In particular, a ``Ghost`` aspect is implicitly added to all
declarations in ``Logging``, so it is not necessary to specify it explicitly.
``Logging`` can be defined either as a local ghost package or as a separate
unit. In the latter case, unit ``Account`` needs to reference unit ``Logging``
in a with-clause like for a non-ghost unit:

.. code-block:: ada

   with Logging;

   package Account is
      ...
   end Account;

Imported Ghost Subprograms
^^^^^^^^^^^^^^^^^^^^^^^^^^

When using manual proof (see :ref:`GNATprove and Manual Proof`), it may be more
convenient to define some properties in the logical language of the prover
rather than in |SPARK|. In that case, ghost functions might be marked as
imported, so that no implementation is needed. For example, the ghost procedure
``Append_To_Log`` seen previously may be defined equivalently as a ghost
imported function as follows:

.. code-block:: ada

   function Append_To_Log (Log : Log_type; Incr : in Integer) return Log_Type with
     Ghost,
     Import;

where ``Log_Type`` is an Ada type used also as placeholder for a type in the
logical language of the prover. To avoid any inconsistency between the
interpretations of ``Log_Type`` in |GNATprove| and in the manual prover, it is
preferable in such a case to mark the definition of ``Log_Type`` as not in
|SPARK|, so that |GNATprove| does not make any assumptions on its content. This
can be achieved by defining ``Log_Type`` as a private type and marking the
private part of the enclosing package as not in |SPARK|:

.. code-block:: ada

   package Logging with
     SPARK_Mode,
     Ghost
   is
      type Log_Type is private;

      function Append_To_Log (Log : Log_type; Incr : in Integer) return Log_Type with
        Import;

      ...

   private
      pragma SPARK_Mode (Off);

      type Log_Type is new Integer;  --  Any definition is fine here
   end Logging;

A ghost imported subprogram cannot be executed, so calls to ``Append_To_Log``
above should not be enabled during compilation, otherwise a compilation error
is issued.

.. _Assertion Pragmas:

Assertion Pragmas
=================

|SPARK| contains features for directing formal verification with
|GNATprove|. These features may also be used by other tools, in particular the
|GNAT Pro| compiler. Assertion pragmas are refinements of pragma ``Assert``
defined in Ada. For all assertion pragmas, an exception ``Assertion_Error`` is
raised at run time when the property asserted does not hold, if the program was
compiled with assertions. The real difference between assertion pragmas is how
they are used by |GNATprove| during proof.

.. _Pragma Assert:

Pragma ``Assert``
-----------------

[Ada 2005]

Pragma ``Assert`` is the simplest assertion pragma. |GNATprove| checks that the
property asserted holds, and uses the information that it holds for analyzing
code that follows. For example, consider two assertions of the same property
``X > 0`` in procedure ``Assert_Twice``:

.. literalinclude:: gnatprove_by_example/examples/assert_twice.adb
   :language: ada
   :linenos:

As expected, the first assertion on line 5 is not provable in absence of a
suitable precondition for ``Assert_Twice``, but |GNATprove| proves that it
holds the second time the property is asserted on line 6:

.. literalinclude:: gnatprove_by_example/results/assert_twice.prove
   :language: none

|GNATprove| considers that an execution of ``Assert_Twice`` with ``X <= 0``
stops at the first assertion that fails. Thus ``X > 0`` when execution reaches
the second assertion.  This is true if assertions are executed at run time, but
not if assertions are discarded during compilation. In the latter case,
unproved assertions should be inspected carefully to ensure that the property
asserted will indeed hold at run time. This is true of all assertion pragmas,
which |GNATprove| analyzes like pragma ``Assert`` in that respect.

.. _Loop Invariants:

Loop Invariants
---------------

[|SPARK|]

Pragma ``Loop_Invariant`` is a special kind of assertion used in
loops. |GNATprove| performs two checks that ensure that the property asserted
holds at each iteration of the loop:

1. `loop invariant initialization`: |GNATprove| checks that the property
   asserted holds during the first iteration of the loop.
2. `loop invariant preservation`: |GNATprove| checks that the property asserted
   holds during an arbitrary iteration of the loop, assuming that it held in
   the previous iteration.

Each of these properties can be independently true or false. For example, in
the following loop, the loop invariant is false during the first iteration and
true in all remaining iterations:

.. literalinclude:: gnatprove_by_example/examples/simple_loops.adb
   :language: ada
   :lines: 6-10

Thus, |GNATprove| checks that property 2 holds but not property 1:

.. literalinclude:: gnatprove_by_example/results/simple_loops.prove
   :language: none
   :lines: 1-2

Conversely, in the following loop, the loop invariant is true during the first
iteration and false in all remaining iterations:

.. literalinclude:: gnatprove_by_example/examples/simple_loops.adb
   :language: ada
   :lines: 12-16

Thus, |GNATprove| checks that property 1 holds but not property 2:

.. literalinclude:: gnatprove_by_example/results/simple_loops.prove
   :language: none
   :lines: 3-4

The following loop shows a case where the loop invariant holds both during the
first iteration and all remaining iterations:

.. literalinclude:: gnatprove_by_example/examples/simple_loops.adb
   :language: ada
   :lines: 18-22

|GNATprove| checks here that both properties 1 and 2 hold:

.. literalinclude:: gnatprove_by_example/results/simple_loops.prove
   :language: none
   :lines: 5-6

But it is not sufficient that a loop invariant is true for |GNATprove| to prove
it. The loop invariant should also be `inductive`: it should be precise enough
that |GNATprove| can check loop invariant preservation by assuming `only` that
the loop invariant held during the last iteration. For example, the following
loop is the same as the previous one, except the loop invariant is true but not
inductive:

.. literalinclude:: gnatprove_by_example/examples/simple_loops.adb
   :language: ada
   :lines: 24-28

|GNATprove| cannot check property 2 on that loop:

.. literalinclude:: gnatprove_by_example/results/simple_loops.prove
   :language: none
   :lines: 7-8

The reasoning of |GNATprove| for checking property 2 in that case can be
summarized as follows:

* Let's take iteration K of the loop, where K > 1 (not the first iteration).
* Let's assume that the loop invariant held during iteration K-1, so we know
  that if K-1 > 1 then Prop holds.
* The previous assumption can be rewritten: if K > 2 then Prop.
* But all we know is that K > 1, so we cannot deduce Prop.

When a loop modifies a collection, which can be either an array or a container
(see :ref:`Formal Containers Library`), it is in general necessary to state in
the loop invariant those parts of the collection that have not been modified up
to the current iteration. This property called `frame condition` in the
scientific literature is essential for |GNATprove|, which otherwise must assume
that all elements in the collection may have been modified. Special care should
be taken to write adequate frame conditions, as they usually look obvious to
programmers, and so it is very common to forget to write them and not being
able to realize what's the problem afterwards. For example, consider the
following loop invariant expressing that, after ``J`` iterations, the part of
the boolean array ``Arr`` already seen has been set to ``True``:

.. literalinclude:: gnatprove_by_example/examples/array_loops.adb
   :language: ada
   :lines: 7-11

|GNATprove| does not prove property 2 in that case:

.. literalinclude:: gnatprove_by_example/results/array_loops.prove
   :language: none
   :lines: 2-3

Let's add a loop invariant stating that the part of the boolean array ``Arr``
not already seen is still set to ``False`` (the frame condition):

.. literalinclude:: gnatprove_by_example/examples/array_loops.adb
   :language: ada
   :lines: 13-18

|GNATprove| is able to prove property 2 with this more precise loop invariant:

.. literalinclude:: gnatprove_by_example/results/array_loops.prove
   :language: none
   :lines: 6-7,9-10

See :ref:`How to Write Loop Invariants` for further guidelines.

Pragma ``Loop_Invariant`` may appear anywhere at the top level of a loop: it is
usually added at the start of the loop, but it may be more convenient in some
cases to add it at the end of the loop, or in the middle of the loop, in cases
where this simplifies the asserted property. In all cases, |GNATprove| checks
loop invariant preservation by reasoning on the virtual loop that starts and
ends at the loop invariant.

It is possible to use multiple loop invariants, which should be grouped
together without intervening statements or declarations. The resulting complete
loop invariant is the conjunction of individual ones. The benefits of writing
multiple loop invariants instead of a conjunction can be improved readability
and better provability (because |GNATprove| checks each pragma
``Loop_Invariant`` separately).

Finally, :ref:`Attribute Loop_Entry` and :ref:`Attribute Update` can be very
useful to express complex loop invariants.

.. note::

   Users that are already familiar with the notion of loop invariant in other
   proof systems should be aware that loop invariants in |SPARK| are slightly
   different from the usual ones. In |SPARK|, a loop invariant must hold when
   execution reaches the corresponding pragma inside the loop. Hence, it needs
   not hold when the loop is never entered, or when exiting the loop.

.. _Loop Variants:

Loop Variants
-------------

[|SPARK|]

Pragma ``Loop_Variant`` is a special kind of assertion used in
loops. |GNATprove| checks that the given scalar value decreases (or increases)
at each iteration of the loop. Because a scalar value is always bounded by its
type in Ada, it cannot decrease (or increase) at each iteration an infinite
number of times, thus one of two outcomes is possible:

1. the loop exits, or
2. a run-time error occurs.

Therefore, it is possible to prove the termination of loops in |SPARK| programs
by proving both a loop variant for each plain-loop or while-loop (for-loops
always terminate in Ada) and the absence of run-time errors.

For example, the while-loops in procedure ``Terminating_Loops`` compute the
value of ``X - X mod 3`` (or equivalently ``X / 3 * 3``) in variable ``Y``:

.. literalinclude:: gnatprove_by_example/examples/terminating_loops.adb
   :language: ada
   :linenos:

|GNATprove| is able to prove both loop variants, as well as absence of run-time
errors in the subprogram, hence that loops terminate:

.. literalinclude:: gnatprove_by_example/results/terminating_loops.prove
   :language: none

Pragma ``Loop_Variant`` may appear anywhere a loop invariant appears. It is
also possible to use multiple loop variants, which should be grouped together
with loop invariants. A loop variant may be more complex than a single
decreasing (or increasing) value, and be given instead by a list of either
decreasing or increasing values (possibly a mix of both). In that case, the
order of the list defines the lexicographic order of progress. See |SPARK| RM
5.5.3 for details.

.. _Pragma Assume:

Pragma ``Assume``
-----------------

[|SPARK|]

Pragma ``Assume`` is a variant of :ref:`Pragma Assert` that does not require
|GNATprove| to check that the property holds. This is used to convey trustable
information to |GNATprove|, in particular properties about external objects
that |GNATprove| has no control upon. |GNATprove| uses the information that the
assumed property holds for analyzing code that follows. For example, consider
an assumption of the property ``X > 0`` in procedure ``Assume_Then_Assert``,
followed by an assertion of the same property:

.. literalinclude:: gnatprove_by_example/examples/assume_then_assert.adb
   :language: ada
   :linenos:

As expected, |GNATprove| does not check the property on line 5, but used it to
prove that the assertion holds on line 6:

.. literalinclude:: gnatprove_by_example/results/assume_then_assert.prove
   :language: none

|GNATprove| considers that an execution of ``Assume_Then_Assert`` with ``X <=
0`` stops at the assumption on line 5, and it does not issue a message in that
case because the user explicitly indicated that this case is not possible. Thus
``X > 0`` when execution reaches the assertion on line 6. This is true if
assertions (of which assumptions are a special kind) are executed at run time,
but not if assertions are discarded during compilation. In the latter case,
assumptions should be inspected carefully to ensure that the property assumed
will indeed hold at run time.

.. _Pragma Assert_And_Cut:

Pragma ``Assert_And_Cut``
-------------------------

[|SPARK|]

Pragma ``Assert_And_Cut`` is a variant of :ref:`Pragma Assert` that allows
hiding some information to |GNATprove|. |GNATprove| checks that the property
asserted holds, and uses *only* the information that it holds for analyzing
code that follows. For example, consider two assertions of the same property
``X = 1`` in procedure ``Forgetful_Assert``, separated by a pragma
``Assert_And_Cut``:

.. literalinclude:: gnatprove_by_example/examples/forgetful_assert.adb
   :language: ada
   :linenos:

|GNATprove| proves that the assertion on line 7 holds, but it cannot prove that
the same assertion on line 12 holds:

.. literalinclude:: gnatprove_by_example/results/forgetful_assert.prove
   :language: none

|GNATprove| *forgets* the exact value of ``X`` after line 9. All it knows is
the information given in pragma ``Assert_And_Cut``, here that ``X > 0``. And
indeed |GNATprove| proves that such an assertion holds on line 11.

Pragma ``Assert_And_Cut`` may be useful in two cases:

1. When the automatic provers are overwhelmed with information from the
   context, pragma ``Assert_And_Cut`` may be used to simplify this context,
   thus leading to more automatic proofs.

2. When |GNATprove| is proving checks for each path through the subprogram (see
   switch ``--proof`` in :ref:`Running GNATprove from the Command Line`), and
   the number of paths is very large, pragma ``Assert_And_Cut`` may be used to
   reduce the number of paths, thus leading to faster automatic proofs.

   For example, consider procedure ``P`` below, where all that is needed to
   prove that the code using ``X`` is free from run-time errors is that ``X``
   is positive. Let's assume that we are running |GNATprove| with switch
   ``--proof=per_path`` so that a formula is generated for each execution path.
   Without the pragma, |GNATprove| considers all execution paths through ``P``,
   which may be many. With the pragma, |GNATprove| only considers the paths
   from the start of the procedure to the pragma, and the paths from the pragma
   to the end of the procedure, hence many fewer paths.

.. code-block:: ada
   :linenos:

   procedure P is
      X : Integer;
   begin
      --  complex computation that sets X
      pragma Assert_And_Cut (X > 0);
      --  complex computation that uses X
   end P;

.. _Overflow Modes:

Overflow Modes
==============

Annotations such as preconditions, postconditions, assertions, loop invariants,
are analyzed by |GNATprove| with the exact same meaning that they have during
execution. In particular, evaluating the expressions in an annotation may raise
a run-time error, in which case |GNATprove| will attempt to prove that this
error cannot occur, and report a warning otherwise.

Integer overflows are a kind of run-time error that occurs when the result of
an arithmetic computation does not fit in the bounds of the machine type used
to hold the result. In some cases, it is convenient to express properties in
annotations as they would be expressed in mathematics, where quantities are
unbounded, for example:

.. code-block:: ada
   :linenos:

    function Add (X, Y : Integer) return Integer with
      Pre  => X + Y in Integer,
      Post => Add'Result = X + Y;

The precondition of ``Add`` states that the result of adding its two parameters
should fit in type ``Integer``. In the default mode, evaluating this expression
will fail an overflow check, because the result of ``X + Y`` is stored in a
temporary of type ``Integer``. If the compilation switch ``-gnato13`` is used,
then annotations are compiled specially, so that arithmetic operations use
unbounded intermediate results. In this mode, |GNATprove| does not generate a
check for the addition of ``X`` and ``Y`` in the precondition of ``Add``, as
there is no possible overflow here.

There are three overflow modes:

* Use base type for intermediate operations (STRICT): in this mode, all
  intermediate results for predefined arithmetic operators are computed using
  the base type, and the result must be in range of the base type.
* Most intermediate overflows avoided (MINIMIZED): in this mode, the compiler
  attempts to avoid intermediate overflows by using a larger integer type,
  typically Long_Long_Integer, as the type in which arithmetic is performed
  for predefined arithmetic operators.
* All intermediate overflows avoided (ELIMINATED): in this mode, the compiler
  avoids all intermediate overflows by using arbitrary precision arithmetic as
  required.

The desired mode for handling intermediate overflow can be specified using
either the Overflow_Mode pragma or an equivalent compiler switch. The pragma
has the form::

    pragma Overflow_Mode ([General =>] MODE [, [Assertions =>] MODE]);

where MODE is one of

* STRICT: intermediate overflows checked (using base type)
* MINIMIZED: minimize intermediate overflows
* ELIMINATED: eliminate intermediate overflows

For example:

.. code-block:: ada

   pragma Overflow_Mode (General => Strict, Assertions => Eliminated);

specifies that general expressions outside assertions be evaluated in the usual
strict mode, and expressions within assertions be evaluated in "eliminate
intermediate overflows" mode. Currently, |GNATprove| only supports pragma
``Overflow_Mode`` being specified in a configuration pragma file.

Additionally, a compiler switch ``-gnato??`` can be used to control the
checking mode default. Here `?` is one of the digits `1` through `3`:

#. use base type for intermediate operations (STRICT)
#. minimize intermediate overflows (MINIMIZED)
#. eliminate intermediate overflows (ELIMINATED)

The switch ``-gnato13``, like the ``Overflow_Mode`` pragma above, specifies that
general expressions outside assertions be evaluated in the usual strict mode,
and expressions within assertions be evaluated in "eliminate intermediate
overflows" mode.

Note that these modes apply only to the evaluation of predefined arithmetic,
membership, and comparison operators for signed integer arithmetic.

For further details of the meaning of these modes, and for further information
about the treatment of overflows for fixed-point and floating-point arithmetic
please refer to the "Overflow Check Handling in GNAT" appendix in the |GNAT Pro|
User's Guide.

.. _Tagged Types and Liskov Substitution Principle:

Tagged Types and Liskov Substitution Principle
==============================================

|SPARK| supports safe Object Oriented Programming by checking behavioral
subtyping between parent types and derived types, a.k.a. Liskov Substitution
Principle: every overriding operation of the derived type should behave so that
it can be substituted for the corresponding overridden operation of the parent
type anywhere.

Class-Wide Subprogram Contracts
-------------------------------

[Ada 2012]

Specific :ref:`Subprogram Contracts` are required on operations of tagged
types, so that |GNATprove| can check Liskov Substitution Principle on every
overriding operation:

* The `class-wide precondition` introduced by aspect ``Pre'Class`` is similar
  to the normal precondition.
* The `class-wide postcondition` introduced by aspect ``Post'Class`` is similar
  to the normal postcondition.

Although these contracts are defined in Ada 2012, they have a stricter meaning
in |SPARK| for checking Liskov Substitution Principle:

* The class-wide precondition of an overriding operation should be weaker (more
  permissive) than the class-wide precondition of the corresponding overridden.
  operation.
* The class-wide postcondition of an overriding operation should be stronger
  (more restrictive) than the class-wide postcondition of the corresponding
  overridden operation.

For example, suppose that the ``Logging`` unit introduced in :ref:`Ghost
Packages` defines a tagged type ``Log_Type`` for logs, with corresponding
operations:

.. literalinclude:: gnatprove_by_example/examples/logging.ads
   :language: ada
   :linenos:

and that this type is derived in ``Range_Logging.Log_Type`` which additionally
keeps track of the minimum and maximum values in the log, so that they can be
accessed in constant time:

.. literalinclude:: gnatprove_by_example/examples/range_logging.ads
   :language: ada
   :linenos:

|GNATprove| proves that the contracts on ``Logging.Append_To_Log`` and its
overriding ``Range_Logging.Append_To_Log`` respect the Liskov Substitution
Principle:

.. literalinclude:: gnatprove_by_example/results/range_logging.prove
   :language: none

Units ``Logging`` and ``Range_Logging`` need not be implemented, or available,
or in |SPARK|. It is sufficient that the specification of ``Logging`` and
``Range_Logging`` are in |SPARK| for this checking. Here, the postcondition of
``Range_Logging.Append_To_Log`` is strictly stronger than the postcondition of
``Logging.Append_To_Log``, as it also specifies the new expected value of the
minimum and maximum values. The preconditions of both procedures are exactly
the same, which is the most common case, but in other cases it might be useful
to be more permissive in the overriding operation's precondition. For example,
``Range_Logging.Append_To_Log`` could allocate dynamically additional memory
for storing an unbounded number of events, instead of being limited to
``Max_Count`` events like ``Logging.Append_To_Log``, in which case its
precondition would be simply ``True`` (the default precondition).

A derived type may inherit both from a parent type and from one or more
interfaces, which only provide abstract operations and no
components. |GNATprove| checks Liskov Substitution Principle on every
overriding operation, both when the overridden operation is inherited from the
parent type and when it is inherited from an interface.

|GNATprove| separately checks that a subprogram implements its class-wide
contract, like for a specific contract.

Mixing Class-Wide and Specific Subprogram Contracts
---------------------------------------------------

[Ada 2012]

It is possible to specify both a specific contract and a class-wide contract on
a subprogram, in order to use a more precise contract (the specific one) for
non-dispatching calls and a contract compatible with the Liskov Substitution
Principle (the class-wide contract) for dispatching calls. In that case,
|GNATprove| checks that:

* The specific precondition is weaker (more permissive) than the class-wide precondition.
* The specific postcondition is stronger (more restrictive) than the class-wide
  postcondition.

For example, ``Logging.Append_To_Log`` could set a boolean flag
``Special_Value_Logged`` when some ``Special_Value`` is appended to the log,
and express this property in its specific postcondition so that it is available
for analyzing non-dispatching calls to the procedure:

.. code-block:: ada

   procedure Append_To_Log (Log : in out Log_Type; Incr : in Integer) with
     Pre'Class  => Log.Log_Size < Max_Count,
     Post'Class => Log.Log_Size = Log.Log_Size'Old + 1,
     Post       => Log.Log_Size = Log.Log_Size'Old + 1 and
                   (if Incr = Special_Value then Special_Value_Logged = True);

This additional postcondition would play no role in dispatching calls, thus it
is not involved in checking the Liskov Substitution Principle. Note that the
absence of specific precondition on procedure ``Append_To_Log`` does not mean
that the default precondition of ``True`` is used: as a class-wide precondition
is specified on procedure ``Append_To_Log``, it is also used as specific
precondition. Similarly, if a procedure has a class-wide contract and a
specific precondition, but no specific postcondition, then the class-wide
postcondition is also used as specific postcondition.

When both a specific contract and a class-wide contract are specified on a
subprogram, |GNATprove| only checks that the subprogram implements its specific
(more precise) contract.

Dispatching Calls and Controlling Operands
------------------------------------------

[Ada 2012]

In a dispatching call, the *controlling operand* is the parameter of class-wide
type whose dynamic type determinates the actual subprogram called. The dynamic
type of this controlling operand may be any type derived from the specific type
corresponding to the classe-wide type of the parameter (the specific type is
``T`` when the class-wide type is ``T'Class``). Thus, in general it is not
possible to know in advance which subprograms may be called in a dispatching
call, when separately analyzing a unit.

In |SPARK|, there is no need to know all possible subprograms called in order
to analyze a dispatching call, which makes it possible for |GNATprove| to
perform this analysis without knowledge of the whole program. As |SPARK|
enforces Liskov Substitution Principle, the class-wide contract of an
overriding operation is always less restrictive than the class-wide contract of
the corresponding overridden operation. Thus, |GNATprove| uses the class-wide
contract of the operation for the specific type of controlling operand to
analyze a dispatching call.

For example, suppose a global variable ``The_Log`` of class-wide type defines
the log that should be used in the program:

.. code-block:: ada

   The_Log : Logging.Log_Type'Class := ...

The call to ``Append_To_Log`` in procedure ``Add_To_Total`` may dynamically
call either ``Logging.Append_To_Log`` or ``Range_Logging.Append_To_Log``:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) is
   begin
      Total := Total + Incr;
      The_Log.Append_To_Log (Incr);
   end Add_To_Total;

Because |GNATprove| separately checks Liskov Substitution Principle for
procedure ``Append_To_Log``, it can use the class-wide contract of
``Logging.Append_To_Log`` for analyzing procedure ``Add_To_Total``.

Dynamic Types and Invisible Components
--------------------------------------

[|SPARK|]

The :ref:`Data Initialization Policy` in |SPARK| applies specially to objects
of tagged type. In general, the dynamic type of an object of tagged type may be
different from its static type, hence the object may have invisible components,
that are only revealed when the object is converted to a class-wide type.

For objects of tagged type, modes on parameters and data dependency contracts
have a different meaning depending on the object's static type:

* For objects of a specific (not class-wide) tagged type, the constraints
  described in :ref:`Data Initialization Policy` apply to the visible
  components of the object only.

* For objects of a class-wide type, the constraints described in :ref:`Data
  Initialization Policy` apply to all components of the object, including
  invisible ones.

|GNATprove| checks during flow analysis that no uninitialized data is read in
the program, and that the specified data dependencies and flow dependencies are
respected in the implementation, based on the semantics above for objects of
tagged type. For example, it detects no issues during flow analysis on
procedure ``Use_Logging`` which initializes parameter ``Log`` and then updates
it:

.. literalinclude:: gnatprove_by_example/examples/use_logging.adb
   :language: ada
   :linenos:

If parameter ``Log`` is of dynamic type ``Logging.Log_Type``, then the call to
``Init_Log`` initializes all components of ``Log`` as expected, and the call to
``Append_To_Log`` can safely read those. If parameter ``Log`` is of dynamic
type ``Range_Logging.Log_Type``, then the call to ``Init_Log`` only initializes
those components of ``Log`` that come from the parent type
``Logging.Log_Type``, but since the call to ``Append_To_Log`` only read those,
then there is no read of uninitialized data. This is in contrast with what
occurs in procedure ``Use_Logging_Classwide``:

.. literalinclude:: gnatprove_by_example/examples/use_logging_classwide.adb
   :language: ada
   :linenos:

on which |GNATprove| issues an error during flow analysis:

.. literalinclude:: gnatprove_by_example/results/use_logging_classwide.flow
   :language: none

Indeed, the call to ``Init_Log`` (a non-dispatching call to
``Logging.Init_Log`` due to the conversion on its parameter) only initializes
those components of ``Log`` that come from the parent type
``Logging.Log_Type``, but the call to ``Append_To_Log`` may read other
components from ``Range_Logging.Log_Type`` which may not be initialized.

A consequence of these rules for data initialization policy is that a parameter
of a specific tagged type cannot be converted to a class-wide type, for example
for a dispatching call. A special aspect ``Extensions_Visible`` is defined in
|SPARK| to allow this case. When ``Extensions_Visible`` is specified on a
subprogram, the data initialization policy for the subprogram parameters of a
specific tagged type requires that the constraints described in :ref:`Data
Initialization Policy` apply to all components of the object, as if the
parameter was of a class-wide type. This allows converting this object to a
class-wide type.

|SPARK| Libraries
=================

.. _Formal Containers Library:

Formal Containers Library
-------------------------

Containers are generic data structures offering a high-level view of
collections of objects, while guaranteeing fast access to their content to
retrieve or modify it. The most common containers are lists, vectors, sets and
maps, which are defined as generic units in the Ada Standard Library. In
critical software where verification objectives severely restrict the use of
pointers, containers offer an attractive alternative to pointer-intensive data
structures.

The Ada Standard Library defines two kinds of containers:

* The controlled containers using dynamic allocation, for example
  ``Ada.Containers.Vectors``. They define containers as controlled tagged
  types, so that memory for the container is automatic reallocated during
  assignement and automatically freed when the container object's scope ends.
* The bounded containers not using dynamic allocation, for example
  ``Ada.Containers.Bounded_Vectors``. They define containers as discriminated
  tagged types, so that the memory for the container can be reserved at
  initialization.

Although bounded containers are better suited to critical software development,
neither controlled containers nor bounded containers can be used in |SPARK|,
because their API does not lend itself to adding suitable contracts (in
particular preconditions) ensuring correct usage in client code.

The formal containers are a variation of the bounded containers with API
changes that allow adding suitable contracts, so that |GNATprove| can prove
that client code manipulates containers correctly. There are 7 formal
containers, which are part of the |GNAT Pro| standard library:

* ``Ada.Containers.Formal_Vectors``
* ``Ada.Containers.Formal_Indefinite_Vectors``
* ``Ada.Containers.Formal_Doubly_Linked_Lists``
* ``Ada.Containers.Formal_Hashed_Sets``
* ``Ada.Containers.Formal_Ordered_Sets``
* ``Ada.Containers.Formal_Hashed_Maps``
* ``Ada.Containers.Formal_Ordered_Maps``

Lists, sets and maps are always bounded. Vectors can be bounded or unbounded
depending on the value of the formal parameter ``Bounded`` when instantiating
the generic unit. Bounded containers do not use dynamic allocation. Unbounded
vectors use dynamic allocation to expand their internal block of memory.

Lists, sets and maps can only be used with definite objects (objects for which
the compiler can compute the size in memory, hence not ``String`` nor
``T'Class``). Vectors come in two flavors for definite objects
(``Formal_Vectors``) and indefinite objects (``Formal_Indefinite_Vectors``).

Modified API of Formal Containers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The visible specification of formal containers is in |SPARK|, with suitable
preconditions on subprograms to ensure correct usage, while their private part
and implementation is not in |SPARK|. Hence, |GNATprove| can be used to prove
correct usage of formal containers in client code, but not to prove that formal
containers implement their specification.

Procedures ``Update_Element`` or ``Query_Element`` that iterate over a
container are not defined on formal containers. Specification and analysis of
such procedures that take an access-to-procedure in parameter is beyond the
capabilities of |SPARK| and |GNATprove|. See :ref:`Excluded Ada Features`.

Procedures and functions that query the content of a container take the
container in parameter. For example, function ``Has_Element`` that queries if a
container has an element at a given position is declared as follows:

.. code-block:: ada

   function Has_Element (Container : T; Position : Cursor) return Boolean;

This is different from the API of controlled containers and bounded containers,
where it is sufficient to pass a cursor to these subprograms, as the cursor
holds a reference to the underlying container:

.. code-block:: ada

   function Has_Element (Position : Cursor) return Boolean;

Cursors of formal containers do not hold a reference to a specific container,
as this would otherwise introduce aliasing between container and cursor
variables, which is not supported in |SPARK|. See :ref:`Absence of
Interference`. As a result, the same cursor can be applied to multiple
container objects.

Three :ref:`Ghost Functions` are defined on formal containers:

* ``Current_To_Last`` returns a copy of a container from a given position (included)
* ``First_To_Previous`` returns a copy of a container up to a given position (excluded)
* ``Strict_Equal`` returns whether two containers are equal in their content and cursors

The purpose of these ghost functions is to facilitate specifying properties of
programs that manipulate formal containers. The linear order of positions is
given by the underlying structure allowing iteration over a container, which
corresponds to the natural order for vectors, lists, ordered sets and ordered
maps.

For example, consider a variant of the ``List.Find`` function defined in the
API of formal containers, which returns a cursor holding the value searched if
there is one, and the special cursor ``No_Element`` otherwise:

.. literalinclude:: gnatprove_by_example/examples/my_find.ads
   :language: ada
   :linenos:

The ghost functions mentioned above are specially useful in :ref:`Loop
Invariants` to refer to parts of containers. For example, here, ghost function
``First_To_Previous`` is used in the loop invariant to specify that the value
searched is not contained in the part of the container already traversed
(otherwise the loop would have exited):

.. literalinclude:: gnatprove_by_example/examples/my_find.adb
   :language: ada
   :linenos:

|GNATprove| proves that function ``My_Find`` implements its specification:

.. literalinclude:: gnatprove_by_example/results/my_find.prove
   :language: none

Function ``Strict_Equal`` is mostly useful to state which parts of a container
have not changed in a loop invariant or a postcondition. For example, it is
used in the postcondition of function ``My_Prepend`` below to state that
``My_Prepend`` does not modify the tail of the list:

.. code-block:: ada
   :linenos:

   procedure My_Prepend (L : in out List; E : Element_Type) with
     Pre  => L.Capacity > Length (L),
     Post => Length (L) = 1 + Length (L'Old) and then
             First_Element (L) = E and then
             Strict_Equal (Current_To_Last(L, First (L'Old)), L'Old);

.. note::

   The behavior of formal containers is defined through :ref:`External
   Axiomatizations`, to facilitate automation of proofs. In this model, the
   behavior of ``Strict_Equal`` is specified based on the logical equality of
   elements instead of the formal parameter ``=`` of the generic in |SPARK|, a
   stronger interpretation made to facilitate automation of proofs. But the
   implementation of ``Strict_Equal`` uses the operation ``=`` on elements
   passes as formal parameter to the generic unit. Thus, an assertion involving
   ``Strict_Equal`` may always hold at run time but not be provable.

Quantification over Formal Containers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:ref:`Quantified Expressions` can be used over the content of a formal
container to express that a property holds for all elements of a container
(using ``for all``) or that a property holds for at least one element of a
container (using ``for some``).

For example, we can express that all elements of a formal list of integers are
prime as follows:

.. code-block:: ada

   (for all Cu in My_List => Is_Prime (Element (My_List, Cu)))

On this expression, the |GNAT Pro| compiler generates code that iterates over
``My_List`` using the functions ``First``, ``Has_Element`` and ``Next`` given
in the ``Iterable`` aspect applying to the type of formal lists, so the
quantified expression above is equivalent to:

.. code-block:: ada

   declare
      Cu     : Cursor_Type := First (My_List);
      Result : Boolean := True;
   begin
      while Result and then Has_Element (My_List, Cu) loop
         Result := Is_Prime (Element (My_List, Cu));
         Cu     := Next (My_List, Cu);
      end loop;
   end;

where ``Result`` is the value of the quantified expression. See |GNAT Pro|
Reference Manual for details on aspect ``Iterable``.
