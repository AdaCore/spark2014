.. _Language Restrictions:

Language Restrictions
=====================

.. _Excluded Ada Features:

Excluded Ada Features
---------------------

To facilitate formal verification, |SPARK| enforces a number of global
simplifications to Ada. The most notable simplifications are:

* Uses of access types and allocators must follow an ownership policy, so that
  only one access object has read-write permission to some allocated memory at
  any given time, or only read-only permission for that allocated memory is
  granted to possibly multiple access objects. See :ref:`Memory Ownership
  Policy`.

* All expressions (including function calls) are free of
  side-effects. Functions with side-effects are more complex to treat logically
  and may lead to non-deterministic evaluation due to conflicting side-effects
  in sub-expressions of an enclosing expression. Functions with side-effects
  should be written as procedures in |SPARK|.

* Aliasing of names is not permitted. Aliasing may lead to unexpected
  interferences, in which the value denoted locally by a given name changes as
  the result of an update to another locally named variable. Formal
  verification of programs with aliasing is less precise and requires more
  manual work. See :ref:`Absence of Interferences`.

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

* Generic code is not analyzed directly. Doing so would require lengthy
  contracts on generic parameters, and would restrict the kind of code that can
  be analyzed, e.g. by forcing the variables read/written by a generic
  subprogram parameter. Instead, instantiations of generic code are analyzed in
  |SPARK|. See :ref:`Analysis of Generics`.

The features listed above are excluded from |SPARK| because, currently, they
defy formal verification. As formal verification technology advances the list
will be revisited and it may be possible to relax some of these
restrictions. There are other features which are technically feasible to
formally verify but which are currently not supported in |SPARK|, such as
access-to-subprogram types.

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

.. literalinclude:: /gnatprove_by_example/examples/validity.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/validity.adb
   :language: ada
   :linenos:

|GNATprove| proves both assertions, but issues warnings about its assumptions
that the evaluation of attribute ``Valid`` on both input parameter ``X`` and
the result of the call to ``Unchecked_Conversion`` return True:

.. literalinclude:: /gnatprove_by_example/results/validity.prove
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

.. literalinclude:: /gnatprove_by_example/examples/data_initialization.ads
   :language: ada
   :linenos:

Procedure ``Proc`` should completely initialize its outputs ``P2`` and ``G2``,
but it only initalizes them partially. Similarly, procedure ``Call_Proc`` which
calls ``Proc`` should completely initalize all of ``Proc``'s inputs prior to
the call, but it only initalizes ``G1`` completely.

.. literalinclude:: /gnatprove_by_example/examples/data_initialization.adb
   :language: ada
   :linenos:

On this program, |GNATprove| issues 6 high check messages, corresponding to
the violations of the data initialization policy:

.. literalinclude:: /gnatprove_by_example/results/data_initialization.flow
   :language: none

While a user can justify individually such messages with pragma ``Annotate``
(see section :ref:`Justifying Check Messages`), it is under her responsibility
to then ensure correct initialization of subcomponents that are read, as
|GNATprove| relies during proof on the property that data is properly
initialized before being read.

Note also the various warnings that |GNATprove| issues on unused parameters,
global items and assignments, also based on the stricter |SPARK| interpretation
of parameter and global modes.

.. _Memory Ownership Policy:

Memory Ownership Policy
-----------------------

In SPARK, access values (a.k.a. pointers) are only allowed to alias in known
ways, so that formal verification can be applied *as if* allocated memory
pointed to by access values was a component of the access value seen as a
record object.

In particular, assignment between access objects operates a transfer of
ownership, where the source object loses its permission to read or write the
underlying allocated memory.

For example, in the following example:

.. literalinclude:: /gnatprove_by_example/examples/ownership_transfer.adb
   :language: ada
   :linenos:

GNATprove correctly detects that ``X.all`` can neither be read nor written
after the assignment of ``X`` to ``Y`` and issues corresponding messages:

.. literalinclude:: /gnatprove_by_example/results/ownership_transfer.flow
   :language: none

At call site, ownership is similarly transferred to the callee's parameters for
the duration of the call, and returned to the actual parameters (a.k.a.
arguments) when returning from the call.

For example, in the following example:

.. literalinclude:: /gnatprove_by_example/examples/ownership_transfer_at_call.adb
   :language: ada
   :linenos:

GNATprove correctly detects that the call to ``Proc`` cannot take ``X`` in
argument as ``X`` is already accessed as a global variable by ``Proc``.

.. literalinclude:: /gnatprove_by_example/results/ownership_transfer_at_call.flow
   :language: none

It is also possible to transfer the ownership of an object temporarily, for
the duration of the lifetime of a local object. This can be achieved by
declaring a local object of an anonymous access type and initializing it with
a part of an existing object. In the following example, ``B`` temporarily
borrows the ownership of ``X``:

.. literalinclude:: /gnatprove_by_example/examples/ownership_borrowing.adb
   :language: ada
   :linenos:

During the lifetime of ``B``, it is incorrect to either read or modify ``X``,
but complete ownership is restored to ``X`` when ``B`` goes out of scope.
GNATprove correctly detects that reading or assigning to ``X`` in the scope of
``B`` is incorrect.

.. literalinclude:: /gnatprove_by_example/results/ownership_borrowing.flow
   :language: none

It is also possible to only transfer read access to a local variable. This
happens when the variable has an anonymous access-to-constant type, as in the
following example:

.. literalinclude:: /gnatprove_by_example/examples/ownership_observing.adb
   :language: ada
   :linenos:

In this case, we say that ``B`` observes the value of ``X``. During the
lifetime of an observer, it is illegal to move or modify the observed object.
GNATprove correctly flags the write inside ``X`` in the scope of ``B`` as
illegal. Note that reading ``X`` is still possible in the scope of ``B``:

.. literalinclude:: /gnatprove_by_example/results/ownership_observing.flow
   :language: none

Only pool-specific access types are allowed in SPARK, so it is not possible to
declare access types with the qualifiers ``all`` or ``const``, as these define
general access types. This ensures in particular that access values in SPARK
always point to dynamically-allocated memory, and thus can be freed when not
null.

.. _Absence of Interferences:

Absence of Interferences
------------------------

In |SPARK|, an assignment to a variable cannot change the value of another
variable. This is enforced by restricting the use of access types (pointers) in
|SPARK|, and by restricting aliasing between parameters and global variables so
that only benign aliasing is accepted (i.e. aliasing that does not cause
interference).

The precise rules detailed in SPARK RM 6.4.2 can be summarized as follows:

* Two mutable parameters should never be aliased.
* An immutable and a mutable parameters should not be aliased, unless the
  immutable parameter is always passed by copy.
* A mutable parameter should never be aliased with a global variable referenced
  by the subprogram.
* An immutable parameter should not be aliased with a global variable
  referenced by the subprogram, unless the immutable parameter is always passed
  by copy.

An immutable parameter is either an input parameter that is not of an access
type, or an anonymous access-to-constant parameter. Except for parameters of
access types, the immutable/mutable distinction is the same as the input/output
one.

These rules extend the existing rules in Ada RM 6.4.1 for restricting aliasing,
which already make it illegal to call a procedure with problematic (non-benign)
aliasing between parameters of scalar type that are `known to denote the same
object` (a notion formally defined in Ada RM).

For example, in the following example:

.. literalinclude:: /gnatprove_by_example/examples/aliasing.ads
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

.. literalinclude:: /gnatprove_by_example/examples/check_param_aliasing.adb
   :language: ada
   :linenos:

|GNATprove| (like |GNAT Pro| compiler, since these are also Ada rules)
correctly detects the two illegal calls and issues errors:

.. literalinclude:: /gnatprove_by_example/results/check_param_aliasing.flow
   :language: none

Here are other examples of correct and incorrect calls (according to SPARK
rules) to procedure ``Whatever``:

.. literalinclude:: /gnatprove_by_example/examples/check_aliasing.adb
   :language: ada
   :linenos:

|GNATprove| correctly detects the two incorrect calls and issues high check
messages:

.. literalinclude:: /gnatprove_by_example/results/check_aliasing.flow
   :language: none
   :lines: 3,5

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
 * calling a procedure with an aspect or pragma ``No_Return`` that has no
   outputs (unless the call is itself inside such a procedure, in which case
   the check is only generated on the call to the enclosing error-signaling
   procedure)

For example, consider the artificial subprogram ``Check_OK`` which raises an
exception when parameter ``OK`` is ``False``:

.. literalinclude:: /gnatprove_by_example/examples/abnormal_terminations.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/abnormal_terminations.adb
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

.. literalinclude:: /gnatprove_by_example/results/abnormal_terminations.prove
   :language: none

|GNATprove| also checks that procedures that are marked with aspect or pragma
``No_Return`` do not return: they should either raise an exception or loop
forever on any input.

.. _Analysis of Generics:

Analysis of Generics
--------------------

|GNATprove| does not directly analyze the code of generics. The following
message is issued if you call |GNATprove| on a generic unit::

  warning: no bodies have been analyzed by GNATprove
  enable analysis of a non-generic body using SPARK_Mode

The advice given is to use ``SPARK_Mode`` on non-generic code, for example an
instantiation of the generic unit. As ``SPARK_Mode`` aspect cannot be attached
to a generic instantiation, it should be specified on the enclosing context,
either through a pragma or aspect.

For example, consider the following generic increment procedure:

.. literalinclude:: /gnatprove_by_example/examples/generic_increment.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/generic_increment.adb
   :language: ada
   :linenos:

Procedure ``Instance_Increment`` is a specific instance of
``Generic_Increment`` for the type ``Integer``:

.. literalinclude:: /gnatprove_by_example/examples/instance_increment.ads
   :language: ada
   :linenos:

|GNATprove| analyzes this instantiation and reports messages on the generic
code, always stating to which instantiation the messages correspond to:

.. literalinclude:: /gnatprove_by_example/results/generic_increment.prove
   :language: none

Thus, it is possible that some checks are proved on an instance and not on
another one. In that case, the chained locations in the messages issued by
|GNATprove| allow you to locate the problematic instantiation. In order to
prove a generic library for all possible uses, you should choose extreme values
for the generic parameters such that, if these instantiations are proved, any
other choice of parameters will be provable as well.
