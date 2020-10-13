Language Restrictions
=====================

Excluded Ada Features
---------------------

To facilitate formal verification, |SPARK| enforces a number of global
simplifications to Ada. The most notable simplifications are:

.. index:: access types; excluded feature

* Uses of access types and allocators must follow an ownership policy, so that
  only one access object has read-write permission to some allocated memory at
  any given time, or only read-only permission for that allocated memory is
  granted to possibly multiple access objects. See :ref:`Memory Ownership
  Policy`.

  .. index:: side effects; excluded feature

* All expressions (including function calls) are free of
  side-effects. Functions with side-effects are more complex to treat logically
  and may lead to non-deterministic evaluation due to conflicting side-effects
  in sub-expressions of an enclosing expression. Functions with side-effects
  should be written as procedures in |SPARK|.

.. index:: aliasing; excluded feature

* Aliasing of names is not permitted. Aliasing may lead to unexpected
  interferences, in which the value denoted locally by a given name changes as
  the result of an update to another locally named variable. Formal
  verification of programs with aliasing is less precise and requires more
  manual work. See :ref:`Absence of Interferences`.

.. index:: goto; excluded feature

* The backward goto statement is not permitted. Backward gotos can be used
  to create loops, which
  require a specific treatment in formal verification, and thus should be
  precisely identified. See :ref:`Loop Invariants` and :ref:`Loop Variants`.

.. index:: controlled types; excluded feature

* The use of controlled types is not permitted. Controlled types lead to the
  insertion of implicit calls by the compiler. Formal verification of implicit
  calls makes it harder for users to interact with formal verification tools,
  as there is no source code on which information can be reported.

.. index:: exceptions; excluded feature

* Handling of exceptions is not permitted. Exception handling gives raise to
  numerous interprocedural control-flow paths. Formal verification of programs
  with exception handlers requires tracking properties along all those paths,
  which is not doable precisely without a lot of manual work. But raising
  exceptions is allowed (see :ref:`Raising Exceptions and Other Error Signaling
  Mechanisms`).

.. index:: termination; excluded feature

* Unless explicitly specified as (possibly) nonreturning, subprograms should
  always terminate when called on inputs satisfying the subprogram
  precondition.  While care is taken in |GNATprove| to reduce possibilities of
  unsoundness resulting from nonreturning subprograms, it is possible that
  axioms generated for nonreturning subprograms not specified as such may lead
  to unsoundness. See :ref:`Nonreturning Procedures`.

.. index:: generics; excluded feature

* Generic code is not analyzed directly. Doing so would require lengthy
  contracts on generic parameters, and would restrict the kind of code that can
  be analyzed, e.g. by forcing the variables read/written by a generic
  subprogram parameter. Instead, instantiations of generic code are analyzed in
  |SPARK|. See :ref:`Analysis of Generics`.

As formal verification technology advances the list
will be revisited and it may be possible to relax some of these
restrictions.

Uses of these features in |SPARK| code are detected by |GNATprove| and reported
as errors. Formal verification is not possible on subprograms using these
features. But these features can be used in subprograms in Ada not identified
as |SPARK| code, see :ref:`Identifying SPARK Code`.

.. index:: Size, Object_Size

Sizes of Objects
----------------

|GNATprove| generally only knows the values of the ``Size`` and ``Object_Size``
attributes in simple cases such as scalar objects. For any more complex types
such as arrays and records, the value of these attributes is unknown, and e.g.
assertions referring to them remain unproved.
The user can indicate the values of these attributes to SPARK via confirming
representation clauses, using ``for Type'Size use ...`` or the aspect syntax
``with Size => ...``. Note that only static values can be used in these
representation clauses.
Note that for an object ``X`` of type ``T``, the value of ``X'Size`` is *not*
necessarily equal to ``T'Size``, but equal to ``T'Object_Size``. So it is
generally more useful to specify ``Object_Size`` on types to be able to know
the value the ``Size`` attribute of the type's objects. However, to compute the
size of ``T'Object_Size`` for composite types, the value of ``C'Size`` is
generally used, ``C`` being the type of a component. The value of
``Object_Size`` must be 8, 16, 32 or a multiple of 64, while the ``Size`` of a
type can be any value.

The following code example shows some simple representation clauses using the
aspect syntax:

.. literalinclude:: /examples/tests/uc/uc.ads
   :language: ada
   :lines: 5-22

.. index:: validity, Unchecked_Conversion, Valid

Data Validity
-------------

|SPARK| reinforces the strong typing of Ada with a stricter initialization
policy (see :ref:`Data Initialization Policy`), and thus provides no means
of specifying that some input data may be invalid. This has some impact on
language features that process or potentially produce invalid values.

Calls to instances of  ``Unchecked_Conversion`` could potentially create
invalid values; however, |SPARK| checks upon creation of such an instance, that
no such invalid values can be produced. Similarly, |SPARK| checks upon
specification of an Address clause or aspect for an object, that no invalid
values can be produced in this way. Conversely, as no invalid values can be
constructed in |SPARK|, the evaluation of the attribute ``Valid`` is assumed to
always return True.

This is illustrated in the following example:

.. literalinclude:: /examples/tests/validity/validity.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/tests/validity/validity.adb
   :language: ada
   :linenos:

|GNATprove| proves both assertions, but issues warnings about its assumptions
that the evaluation of attribute ``Valid`` on both input parameter ``X`` and
the result of the call to ``Unchecked_Conversion`` return True. It also issues
a "high" unproved check that the unchecked conversion to ``Float`` may produce
invalid values (for example, if an ``Integer`` is converted whose bit
representation corresponds to a ``NaN`` float, which is not allowed in SPARK).

.. literalinclude:: /examples/tests/validity/test.out
   :language: none

When checking an instance of ``Unchecked_Conversion``, |GNATprove| also checks
that both types have the same ``Object_Size``. For non-scalar types,
|GNATprove| doesn't know the ``Object_Size`` of the types, so representation
clauses that specify ``Object_Size`` are required to prove such checks (see
also :ref:`Sizes of Objects`). Similarly, for object declarations with an
Address clause or aspect that refers to the ``'Address`` of another object,
|SPARK| checks that both objects have the same known ``Object_Size``.

The following example shows some typical usages of unchecked conversions and
``Object_Size`` clauses:

.. literalinclude:: /examples/tests/uc/uc.ads
   :language: ada
   :linenos:

.. index:: initialization
           Relaxed_Initialization; initialization policy

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

.. literalinclude:: /examples/tests/data_initialization/data_initialization.ads
   :language: ada
   :linenos:

Procedure ``Proc`` should completely initialize its outputs ``P2`` and ``G2``,
but it only initalizes them partially. Similarly, procedure ``Call_Proc`` which
calls ``Proc`` should completely initalize all of ``Proc``'s inputs prior to
the call, but it only initalizes ``G1`` completely.

.. literalinclude:: /examples/tests/data_initialization/data_initialization.adb
   :language: ada
   :linenos:

On this program, |GNATprove| issues 6 high check messages, corresponding to
the violations of the data initialization policy:

.. literalinclude:: /examples/tests/data_initialization/test.out
   :language: none

While a user can justify individually such messages with pragma ``Annotate``
(see section :ref:`Justifying Check Messages`), it is under her responsibility
to then ensure correct initialization of subcomponents that are read, as
|GNATprove| relies during proof on the property that data is properly
initialized before being read.

Note also the various low check messages and warnings that |GNATprove| issues
on unused parameters, global items and assignments, also based on the stricter
|SPARK| interpretation of parameter and global modes.

It is possible to opt out of the strong data initialization
policy of |SPARK| on a case by case basis using the aspect
``Relaxed_Initialization`` (see section :ref:`Aspect Relaxed_Initialization`).
Parts of objects subjected to this aspect only need to be initialized when
actually read. Using ``Relaxed_Initialization`` requires specifying data
initialization through contracts that are verified by proof (as opposed to
flow analysis). Thus, ``Relaxed_Initialization`` should only be used when
needed as it requires more effort to verify data initialization from both the
user and the tool.

.. index:: access types; ownership policy
           ownership

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

.. literalinclude:: /examples/tests/ownership_transfer/ownership_transfer.adb
   :language: ada
   :linenos:

GNATprove correctly detects that ``X.all`` can neither be read nor written
after the assignment of ``X`` to ``Y`` and issues corresponding messages:

.. literalinclude:: /examples/tests/ownership_transfer/test.out
   :language: none

At call site, ownership is similarly transferred to the callee's parameters for
the duration of the call, and returned to the actual parameters (a.k.a.
arguments) when returning from the call.

For example, in the following example:

.. literalinclude:: /examples/tests/ownership_transfer_at_call/ownership_transfer_at_call.adb
   :language: ada
   :linenos:

GNATprove correctly detects that the call to ``Proc`` cannot take ``X`` in
argument as ``X`` is already accessed as a global variable by ``Proc``.

.. literalinclude:: /examples/tests/ownership_transfer_at_call/test.out
   :language: none
   :lines: 56-58

It is also possible to transfer the ownership of an object temporarily, for
the duration of the lifetime of a local object. This can be achieved by
declaring a local object of an anonymous access type and initializing it with
a part of an existing object. In the following example, ``B`` temporarily
borrows the ownership of ``X``:

.. literalinclude:: /examples/tests/ownership_borrowing/ownership_borrowing.adb
   :language: ada
   :linenos:

During the lifetime of ``B``, it is incorrect to either read or modify ``X``,
but complete ownership is restored to ``X`` when ``B`` goes out of scope.
GNATprove correctly detects that reading or assigning to ``X`` in the scope of
``B`` is incorrect.

.. literalinclude:: /examples/tests/ownership_borrowing/test.out
   :language: none

It is also possible to only transfer read access to a local variable. This
happens when the variable has an anonymous access-to-constant type, as in the
following example:

.. literalinclude:: /examples/tests/ownership_observing/ownership_observing.adb
   :language: ada
   :linenos:

In this case, we say that ``B`` observes the value of ``X``. During the
lifetime of an observer, it is illegal to move or modify the observed object.
GNATprove correctly flags the write inside ``X`` in the scope of ``B`` as
illegal. Note that reading ``X`` is still possible in the scope of ``B``:

.. literalinclude:: /examples/tests/ownership_observing/test.out
   :language: none

Only pool-specific access types are allowed in SPARK, so it is not possible to
declare access types with the qualifiers ``all`` or ``const``, as these define
general access types. This ensures in particular that access values in SPARK
always point to dynamically-allocated memory, and thus can be freed when not
null.

.. index:: aliasing; absence of interference

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

.. literalinclude:: /examples/tests/aliasing/aliasing.ads
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

.. literalinclude:: /examples/tests/check_param_aliasing/check_param_aliasing.adb
   :language: ada
   :linenos:

|GNATprove| (like |GNAT Pro| compiler, since these are also Ada rules)
correctly detects the two illegal calls and issues errors:

.. literalinclude:: /examples/tests/check_param_aliasing/test.out
   :language: none

Here are other examples of correct and incorrect calls (according to SPARK
rules) to procedure ``Whatever``:

.. literalinclude:: /examples/tests/check_aliasing/check_aliasing.adb
   :language: ada
   :linenos:

|GNATprove| correctly detects the two incorrect calls and issues high check
messages:

.. literalinclude:: /examples/tests/check_aliasing/test.out
   :language: none
   :lines: 10-12,18-20

Note that |SPARK| currently does not detect aliasing between objects that
arises due to the use of Address clauses or aspects.

.. index:: exceptions; raising exception
           No_Return; error signaling

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
   outputs (unless the call is itself inside a (possibly) nonreturning
   procedure, see :ref:`Nonreturning Procedures`, in which case the check
   is only generated on the call to the enclosing error-signaling procedure
   if any)

For example, consider the artificial subprogram ``Check_OK`` which raises an
exception when parameter ``OK`` is ``False``:

.. literalinclude:: /examples/tests/abnormal_terminations/abnormal_terminations.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/tests/abnormal_terminations/abnormal_terminations.adb
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

.. literalinclude:: /examples/tests/abnormal_terminations/test.out
   :language: none

|GNATprove| also checks that procedures that are marked with aspect or pragma
``No_Return`` do not return: they should either raise an exception or loop
forever on any input.

.. index:: No_Return; nonreturning procedures
           Might_Not_Return

Nonreturning Procedures
-----------------------

|GNATprove| assumes that, unless explicitly specified as (possibly)
nonreturning, subprograms should always terminate when called on inputs
satisfying the subprogram precondition. In particular, functions should
always terminate. Procedures might not terminate, in which case they
should be annotated with a suitable pragma or aspect:

* ``No_Return`` to specify that the procedure never returns. This is a
  nonreturning procedure.

* ``Annotate Might_Not_Return`` to specify that the procedure might not
  return in some cases. This is a possibly nonreturning procedure.

Nonreturning and possibly nonreturning procedures are handled differently.
It is an error to call a possibly nonreturning procedure from a function
or from a procedure that is not itself (possibly) nonreturning.
Calling a nonreturning procedure from a procedure that is not
itself (possibly) nonreturning leads to a check that the call is unreachable.
Such a call is in effect interpreted as an error signaling mechanism
(see :ref:`Raising Exceptions and Other Error Signaling Mechanisms`).

For example, consider the procedure ``Conditional_Exit`` which conditionally
calls the nonterminating ``Always_Exit`` procedure:

.. literalinclude:: /examples/tests/possibly_nonreturning/possibly_nonreturning.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/tests/possibly_nonreturning/possibly_nonreturning.adb
   :language: ada
   :linenos:

|GNATprove| issues an error here on the call to the possibly nonreturning
procedure ``Conditional_Exit`` in procedure ``Regular``:

.. literalinclude:: /examples/tests/possibly_nonreturning/test.out
   :language: none

It would be legal to call the nonreturning procedure ``Always_Exit`` from
procedure ``Regular`` though, in which case it will be interpreted as
an error signaling mechanism, and |GNATprove| will attempt to prove that
the call is unreachable.

Note that it is also possible to specify explicitly that a subprogram
terminates, in which case |GNATprove| will verify that it indeed terminates.
See :ref:`Subprogram Termination`.

.. index:: generics; analysis of instances

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

.. literalinclude:: /examples/tests/instance_increment/generic_increment.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/tests/instance_increment/generic_increment.adb
   :language: ada
   :linenos:

Procedure ``Instance_Increment`` is a specific instance of
``Generic_Increment`` for the type ``Integer``:

.. literalinclude:: /examples/tests/instance_increment/instance_increment.ads
   :language: ada
   :linenos:

|GNATprove| analyzes this instantiation and reports messages on the generic
code, always stating to which instantiation the messages correspond to:

.. literalinclude:: /examples/tests/instance_increment/test.out
   :language: none

Thus, it is possible that some checks are proved on an instance and not on
another one. In that case, the chained locations in the messages issued by
|GNATprove| allow you to locate the problematic instantiation. In order to
prove a generic library for all possible uses, you should choose extreme values
for the generic parameters such that, if these instantiations are proved, any
other choice of parameters will be provable as well.
