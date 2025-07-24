Subprogram Contracts
====================

The most important feature to specify the intended behavior of a |SPARK|
program is the ability to attach a contract to subprograms. In this document, a
`subprogram` can be a procedure, a function or a protected entry. This contract
is made up of various optional parts:

* The `precondition` introduced by aspect ``Pre`` specifies constraints on
  callers of the subprogram.
* The `postcondition` introduced by aspect ``Post`` specifies (partly or
  completely) the functional behavior of the subprogram.
* The `contract cases` introduced by aspect ``Contract_Cases`` is a way to
  partition the behavior of a subprogram. It can replace or complement a
  postcondition.
* The `data dependencies` introduced by aspect ``Global`` specify the global
  data read and written by the subprogram.
* The `flow dependencies` introduced by aspect ``Depends`` specify how
  subprogram outputs depend on subprogram inputs.
* The `exceptional contract` introduced by aspect ``Exceptional_Cases``
  specifies the exceptions that might be propagated by a procedure, along with
  exceptional postconditions.
* The `program exit contract` introduced by aspect ``Program_Exit`` specifies
  in which cases a subprogram might terminate the program abruptly.
* The `exit cases` introduced by aspect ``Exit_Cases`` is a way to specify how
  a subprogram is allowed to exit by partioning the input domain. It can replace
  or complement a postcondition or an exceptional contract.
* The `termination contract` introduced by aspect ``Always_Terminates``
  requires procedures and entries to terminate, possibly under a particular
  condition.
* The `subprogram variant` introduced by aspect ``Subprogram_Variant`` is
  used to ensure termination of recursive subprograms.

Which contracts to write for a given verification objective, and how
|GNATprove| generates default contracts, is detailed in :ref:`How to Write
Subprogram Contracts`.

|GNATprove| formally verifies that each execution of each |SPARK| subprogram it
analyzes will either:

* return normally in a state that respects the subprogram’s postcondition,
* raise an exception in a state that respects the subprogram's exceptional
  contract,
* terminate abnormally as a result of a primary stack, secondary stack, or heap
  memory allocation failure, or
* not terminate at all when it is allowed by its termination contract.

|GNATprove| also checks that procedures that are marked with aspect or pragma
``No_Return`` do not return: they should either raise an exception, call a
non-returning subprogram, or loop forever on any input.

.. index:: precondition
           see: Pre; precondition
           seealso: Gold level; precondition
           Assertion_Policy; for precondition
           exceptions; in precondition

Preconditions
-------------

*Supported in Ada 2012*

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
the shortcut boolean operator ``and then`` instead of ``and``, so that calling
the procedure in a context where ``Incr`` is negative does not result in an
overflow when evaluating ``Integer'Last - Incr``. Instead, the use of ``and
then`` ensures that a precondition failure will occur before the expression
``Integer'Last - Incr`` is evaluated.

.. note::

   It is good practice to use the shortcut boolean operator ``and then``
   instead of ``and`` in preconditions. This is required in some cases by
   |GNATprove| to prove absence of run-time errors inside preconditions.

Raise expressions occuring in preconditions are handled in a special way.
Indeed, it is a common pattern to use a raise expression to change the
exception raised by a failed precondition. To support this use case, raising
an expression in a precondition is considered in |SPARK| to be a failure of the
precondition, as opposed to a runtime failure, which would not be allowed in
|SPARK|. As an example, we may want to introduce specific exceptions for the
the failure of each part of the precondition of ``Add_To_Total``, so as to
debug them more easily. This can be done by using two raise expressions as in
the following snippet:

.. code-block:: ada

   Negative_Increment  : exception;
   Total_Out_Of_Bounds : exception;

   procedure Add_To_Total (Incr : in Integer) with
     Pre => (Incr >= 0 or else raise Negative_Increment)
     and then (Total in 0 .. Integer'Last - Incr
               or else raise Total_Out_Of_Bounds);

The raise expressions are associated to each conjunct using an ``or else``
short circuit operator, so that they will be evaluated when the conjunct
evaluates to ``False`` and the exception will be raised.

On this code, |GNATprove| will not attempt to verify that the exceptions can
never be raised when evaluating the precondition in any context, like it does
for other runtime exceptions. Instead, it will consider them being raised as a
failure of the precondition. So, for |GNATprove|, the precondition with
the raise expressions above is effectively equivalent to the precondition of
the previous example.

.. index:: postcondition
           see: Post; postcondition
           seealso: Gold level; postcondition

Postconditions
--------------

*Supported in Ada 2012*

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

.. index:: Contract_Cases
           seealso: Gold level; Contract_Cases

Contract Cases
--------------

*Specific to SPARK*

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

.. index:: Global; in subprogram contract
           global variables; in Global contract
           seealso: Bronze level; Global

Data Dependencies
-----------------

*Specific to SPARK*

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

For protected subprograms, the protected object is considered as an implicit
parameter of the subprogram:

* it is an implicit parameter of mode ``in`` of a protected function; and
* it is an implicit parameter of mode ``in out`` of a protected procedure or a
  protected entry.

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

.. index:: Depends; in subprogram contract
           global variables; in Depends contract
           seealso: Bronze level; Depends

Flow Dependencies
-----------------

*Specific to SPARK*

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

Outputs (both parameters and global variables) may have an implicit input part
depending on their type:

* an unconstrained array ``A`` has implicit input bounds ``A'First`` and
  ``A'Last``
* a discriminated record ``R`` has implicit input discriminants, for example
  ``R.Discr``

Thus, an output array ``A`` and an output discriminated record ``R`` may appear
in input position inside a flow-dependency contract, to denote the input value
of the bounds (for the array) or the discriminants (for the record).

For protected subprograms, the protected object is considered as an implicit
parameter of the subprogram which may be mentioned in the flow dependencies,
under the name of the protected unit (type or object) being declared:

* as an implicit parameter of mode ``in`` of a protected function, it can be
  mentioned on the right-hand side of flow dependencies; and
* as an implicit parameter of mode ``in out`` of a protected procedure or a
  protected entry, it can be mentioned on both sides of flow dependencies.

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
value, the corresponding flow dependency can use the shorthand symbol ``+`` to
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

.. index:: state abstraction; in subprogram contract

Abstraction and Contracts
-------------------------
Just like for programming, abstraction is a key concept for the scalability
of formal verification. In Ada, it is usually provided through packages and
privacy. A package is composed of (at most) three parts, the public part of the
specification, its private part, and the package body. Entities defined in the
private part of the specification or the package body cannot be used in the
public part of the specification nor in other units.

.. index:: Refined_Global, Refined_Depends

State Abstraction and Dependencies
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
*Specific to SPARK*

The subprogram contracts mentioned so far always used directly global
variables. In many cases, this is not possible because the global variables are
defined in another unit and not directly visible (because they are defined in
the private part of a package specification, or in a package
implementation). The notion of abstract state in |SPARK| can be used in that
case (see :ref:`State Abstraction`) to name in contracts global data that is
not visible.

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

Then, the implementations of ``Init_Total`` and ``Add_To_Total`` can
define refined data and flow dependencies introduced respectively by
``Refined_Global`` and ``Refined_Depends``, which give the precise
dependencies for these subprograms in terms of concrete variables:

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

* each abstract global input has at least one of its constituents
  mentioned by the concrete global inputs
* each abstract global in_out has at least one of its constituents
  mentioned with mode input and one with mode output (or at least one
  constituent with mode in_out)
* each abstract global output has to have all its constituents
  mentioned by the concrete global outputs
* the concrete flow dependencies are a subset of the abstract flow
  dependencies

|GNATprove| uses the abstract contract (data and flow dependencies) of
``Init_Total`` and ``Add_To_Total`` when analyzing calls outside package
``Account`` and the more precise refined contract (refined data and flow
dependencies) of ``Init_Total`` and ``Add_To_Total`` when analyzing calls
inside package ``Account``.

Refined dependencies can be specified on both subprograms and tasks for which
data and/or flow dependencies that are specified include abstract states which
are refined in the current unit.

.. index:: expression function; in refinement, Refined_Post

Abstraction and Functional Contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Abstraction affects how functional contracts are written. First,
if global variables are not visible for data dependencies, they are not visible
either for functional contracts. For example, in the case of procedure
``Add_To_Total``, if global variable ``Total`` is not visible, we cannot
express anymore the precondition and postcondition of ``Add_To_Total`` as in
:ref:`Preconditions` and :ref:`Postconditions`. In this case, it is necessary
to define accessor functions to retrieve properties of the state that are needed
to express contracts. For example here:

.. code-block:: ada

   function Get_Total return Integer;

   procedure Add_To_Total (Incr : in Integer) with
     Pre  => Incr >= 0 and then Get_Total in 0 .. Integer'Last - Incr,
     Post => Get_Total = Get_Total'Old + Incr;

The body of the function ``Get_Total`` may be defined either in the private part
of package ``Account`` or in its implementation. It may take the form of a
regular function or an expression function (see :ref:`Expression Functions`):

.. code-block:: ada

   Total : Integer;

   function Get_Total return Integer is (Total);

Accessor functions can be annotated as :ref:`Ghost Functions` functions to
prevent them from being available in the standard API of the package.

Abstraction also affects the visibility of contracts by
the verification tool. By default, the notion of visibility used by |GNATprove|
is rather liberal: subprogram contracts and bodies of expression functions are
visible except if they occur in the body of another (possibly nested) unit. In
particular, contracts of subprograms declared in the private part of other units
are visible. On our example, the precise
definition of ``Get_Global`` is visible for the verification of ``Account`` no
matter whether it is declared in its private part or its implementation.
However, it will only be available when verifying units using the
``Account`` package if it is declared in its private part. To demonstrate this,
we can introduce two distinct functions to access the value of ``Total`` in
the public part of the specification of ``Account``:

.. code-block:: ada

   function Get_Total_1 return Integer;

   function Get_Total_2 return Integer;

They can be defined as expression functions as done previously, either in
private part of ``Account`` or in its implementation:

.. code-block:: ada

   function Get_Total_1 return Integer is (Total);

   function Get_Total_2 return Integer is (Total);

In both cases, it will be possible to prove that ``Get_Total_1`` and
``Get_Total_2`` necessarily return the same value when verifying ``Account``
and all subprograms declared within. However, in a ``Main`` procedure using
the ``Account`` package, this property would no longer be provable if the
expression functions are supplied in the body of ``Account``.

Note that abstraction is an important concept for verification as it
ensures scalability of complex proofs by enforcing separation of concerns -
i.e. only the information that is necessary for a given verification is
available in the verification tool. The default visibility rules for
verification can be tuned in some cases using the annotations ``Hide_Info`` and
``Unhide_Info``, see :ref:`Annotation for Managing the Proof Context`, to
achieve a fine-grained abstraction.

The examples presented so far take advantage of the specific handling of
expression functions to provide different contracts for a subprogram.
Since the body of expression functions acts as an implicit postcondition, it
directly provides a `refined` version of the function's contract possibly with
a different visibility. Not all subprograms can be turned into an expression
function. As an alternative, the |SPARK| language provides the ``Refined_Post``
aspect or pragma that can be used to provide an alternative postcondition on a
subprogram body. For example, procedure ``Add_To_Total`` may also increment the
value of a counter ``Call_Count`` at each call. If this information is not
relevant for the verification of programs using the ``Account`` package, it can
be expressed in a refined postcondition:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Refined_Post => Total = Total'Old + Incr and Call_Count = Call_Count'Old + 1
   is
      ...
   end Add_To_Total;

|GNATprove| uses the abstract contract (precondition and postcondition) of
``Add_To_Total`` when analyzing calls outside package ``Account`` and the more
precise refined contract (precondition and refined postcondition) of
``Add_To_Total`` when analyzing calls inside package ``Account``.
The verification of the subprogram itself ensures that the refined contracts
are a `refinement` of the abstract ones: the postcondition of
``Add_To_Total`` should be implied by its refined postcondition only, without
looking at its body. As an example, removing the first conjunct in the refined
postcondition of ``Add_To_Total`` would cause the verification of its
postcondition to fail even though it is still implied by its implementation:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Refined_Post => Call_Count = Call_Count'Old + 1 -- NOT PRECISE ENOUGH TO PROVE THE POST
   is
      ...
   end Add_To_Total;

.. index:: exceptions; Exceptional_Cases

Exceptional Contracts
---------------------

*Specific to SPARK*

In SPARK, every subprogram with side effects which might propagate an exception
should be annotated with an exceptional contract. This contract, introduced by
the ``Exceptional_Cases`` aspect, lists all the exceptions which might be
propagated by a procedure, and associates them to an exceptional postcondition.
This postcondition describes the effect of the procedure when the exception is
raised. As an example, consider the procedure ``Incr_All`` below. It goes over
an array to increment its elements. If an overflow would occur, the exception
``Overflow`` is raised and the traversal is stopped. The global variable
``Index`` is used to store the current index at this point. The exceptional
contract of ``Incr_All`` states both that it might propagate ``Overflow``, and
that it will only do so if it finds an offending index, using the global
variable ``Index``. The fact that ``Overflow`` is necessarily raised
when such an index exists follows from the regular postcondition of
``Incr_All``:

.. literalinclude:: /examples/ug__exceptions/exceptions.adb
   :language: ada
   :linenos:

|GNATprove| can successfully verify both ``Incr_All`` above and its two callers:
the exception is handled inside ``Incr_All_Cond`` and the
call to ``Incr_All`` never raises ``Overflow`` in ``Incr_All_With_Pre``.

.. literalinclude:: /examples/ug__exceptions/test.out
   :language: none

The :ref:`Data Initialization Policy` of SPARK is mostly enforced on exceptional
exit of subprograms. All global outputs shall be initialized when an exception
is propagated, like ``Index`` in the example above. It is the case too for
parameters which are necessarily passed by reference (tagged types, aliased
parameters...). Other parameters, either necessarily passed by copy or for
which the parameter passing mode is unspecified by the language, do not need
to be initialized. As a result, after a call which has propagated an exception:

* output parameters necessarily passed by reference are considered to have been
  initialized or updated by the call as on a normal return,
* output parameters necessarily passed by copy are preserved, and
* output parameters for which the parameter passing mode is unspecified by the
  language are considered to not be initialized anymore; they should not be
  read after the call.

As an example, the parameter ``A`` of ``Incr_All`` is a composite type
containing only subcomponents of a by-copy type (a scalar). As per the Ada
reference manual, its parameter passing mode is unspecified. It means that
its value will be unspecified if the call to ``Incr_All`` raises an exception,
as can be seen on ``Incr_All_Bad_Init``:

.. literalinclude:: /examples/ug__exceptions_bad_init/exceptions_bad_init.adb
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__exceptions_bad_init/test.out
   :language: none

Note that, even though access types are passed by copy, ``in`` parameters of an
access-to-variable part can be safely used after an exceptional exit as only
the designated value can be modified.

To make it easier for the user, it is not allowed to mention parameters which
are not necessarily passed by reference in an exceptional postcondition.
An error is emitted if the exceptional postcondition of ``Incr_All`` is
modified to mention ``A``:

.. literalinclude:: /examples/ug__exceptions_bad/exceptions_bad.adb
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__exceptions_bad/test.out
   :language: none

The exceptional contract is allowed if the parameter ``A`` is marked as
``aliased`` however, as it is then necessarily passed by reference:

.. literalinclude:: /examples/ug__exceptions_post/exceptions_post.adb
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__exceptions_post/test.out
   :language: none

Note that only exceptions which are raised explicitly in the code
can be handled or propagated. For example, it would not be possible to remove
the defensive code raising the exception in the loop and instead propagate
``Constraint_Error`` directly as in ``Incr_All_CE``. Indeed, |GNATprove|
always attempts to prove that runtime checks never fail. It complains
on ``Incr_All_CE`` that the range check might fail, and flags the exceptional
case as unreachable if proof warnings are enabled:

.. literalinclude:: /examples/ug__exceptions_rte/exceptions_rte.adb
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__exceptions_rte/test.out
   :language: none

If the exception raised by a raise statement or procedure call is neither
handled nor allowed by its exceptional contract (that is, it has no associated
exceptional postcondition or this postcondition is statically False), then it
is unexpected and
|GNATprove| will make sure that it never occurs. More precisely,
|GNATprove| treats raising an unexpected exception in the following way:

 * in flow analysis, the program paths that lead to a statement raising an
   unexpected exception are not considered when checking the contract of the
   subprogram; and
 * in proof, a check is generated for these statements, to prove that
   no such program point is reachable.

Occurences of  ``pragma Assert (X)`` where ``X`` is an expression statically
equivalent to ``False`` are treated in the same way.

As an example, consider the artificial subprogram ``Check_OK`` which raises an
exception when parameter ``OK`` is ``False``. The ``Check_OK`` procedure does
not have an exceptional contract so the exception is unexpected:

.. literalinclude:: /examples/ug__abnormal_terminations/abnormal_terminations.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__abnormal_terminations/abnormal_terminations.adb
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

.. literalinclude:: /examples/ug__abnormal_terminations/test.out
   :language: none

.. note::

   Raising an exception is a side-effect. As a consequence, the aspect
   ``Exceptional_Cases`` is not allowed on functions which are not annotated
   with the ``Side_Effects`` aspect and exceptions raised
   by ``raise_expressions`` cannot be handled or propagated. |GNATprove|
   makes sure that they never occur.

.. index:: Program_Exit

Contract for Abrupt Program Termination
---------------------------------------

*Specific to SPARK*

A subprogram might sometimes cause the whole program to terminate abruptly. In
general, this might happen either by mistake, because of a runtime error or an
unexpected exception, or on purpose, for example because of an explicit call to
``GNAT.OS_Lib.OS_Exit``. Unintended cases are ruled out in |SPARK|, as runtime
errors (except for excessive memory usage) and unexpected exceptions are
detected by |GNATprove|. Intended cases are allowed, but a subprogram with side
effects that is supposed to potentially exit the whole program shall be
annotated with the ``Program_Exit`` aspect. The boolean expression given by
this aspect, if any, shall be true when the program is terminated.
It can be used to reason about intended program termination. As an example,
consider the following package:

.. literalinclude:: /examples/ug__abrupt_program_exit/abrupt_program_exit.ads
   :language: ada
   :linenos:

The ``Do_Exit`` procedure prints the error message ``Msg`` on standard error and
terminates the program with the error code ``Status``. The
``Error_Message_Type`` type is a tagged type that can be extanded by users of
the library to encode their own error message. It has a ``To_String`` primitive
used for printing the error message. The ghost functions ``Error_Status`` and
``Error_Message`` allow callers of ``Do_Exit`` to specify and
verify properties about potential abrupt terminations. The boolean expression
of the ``Program_Exit`` aspect on ``Do_Exit`` links the results of
these ghost functions to the ``Status`` and ``Msg`` parameters of ``Do_Exit``.
Note that, even if it might terminate the program abruptly, ``Do_Exit`` can be
annotated with ``Always_Terminates``. Exiting the program abruptly is considered
as a valid termination. The ``No_Return`` aspect states that ``Do_Exit``
never returns normally - it is compatible with the ``Always_Terminates``,
``Do_Exit`` always terminates abnormally.

These contracts allow verifying other subprograms that use ``Do_Exit`` to
terminate the program abruptly. As an example, consider the ``Get_Digit``
procedure that reads a digit on standard input and terminates the program if the
input is ill-formed and the function which side effects ``Add`` that adds two
digits and terminates the program if the result exceeds 10:

.. literalinclude:: /examples/ug__abrupt_program_exit/use_abrupt_program_exit.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__abrupt_program_exit/use_abrupt_program_exit.adb
   :language: ada
   :linenos:

The procedures ``Play`` and ``Auto_Play`` call the ``Get_Digit`` and ``Add``
procedures. They propose a game where the user chooses two
digits which are then added by the program. The program exit condition of
``Play`` uses ``Error_Status`` and ``Error_Message`` to reason about the
different cases in which the program might abruptly terminate. The
procedure ``Auto_Play`` simulates a valid game, so it cannot cause an abrupt
exit of the program.

When a subprogram that might terminate the program is called,
|GNATprove| verifies the program exit condition of the caller.
If the caller has no ``Program_Exit`` aspect, it
means that it is not allowed to terminate the program, and |GNATprove| verifies
that either the call itself cannot occur - the branch is dead - or the called
subprogram cannot exit the program - its ``Program_Exit`` aspect does not allow
it.
In our example, the program exit condition of ``Do_Exit`` is enough to prove
the program exit conditions of ``Get_Digit``, ``Add``, and then ``Play``
afterwards. As the program exit condition of ``Add`` states that
the program can only be exited if ``X + Y`` is at least 10, |GNATprove| can
check that it can safely be called inside ``Auto_Play``:

.. literalinclude:: /examples/ug__abrupt_program_exit/test.out
   :language: none

As it should hold when the program terminates, the program exit condition is a
postcondition. It can reference inputs of the subprogram, both global objects
and parameters, potentially using the ``Old`` attribute if they can be modified
by the subprogram. It can also reference global outputs in the post state (after
the call), like ``Error_State`` here, but not parameters. Unlike for normal
return and exception propagation, it is not necessary to leave outputs in a
clean state when exiting the whole program, as their values cannot be used
afterwards. In particular, |GNATprove| does not enforce initialization,
reclamation, nor alias freedom on such outputs, unless they are mentioned in
the program exit condition (in which case they need to be readable there).
For example, when exiting from ``Get_Digit``, |GNATprove| only enforces the
initialization of ``Error_State``, but not of ``X``.

.. note::

   Currently, there is no way to intentionally terminate the program abruptly in
   SPARK. The body of leaf subprograms doing so will typically be either in
   full Ada, like the subprograms in the package ``Abrupt_Program_Exit`` below,
   or in another language like C:

   .. literalinclude:: /examples/ug__abrupt_program_exit/abrupt_program_exit.adb
      :language: ada
      :linenos:

.. index:: Exit_Cases

Exit Cases
----------

*Specific to SPARK*

There are several ways for a subprogram to terminate: it can return normally,
propagate an exception, or exit the program abruptly. If a subprogram does
not always terminate normally, then it can have an
``Exit_Cases`` aspect. This aspect allows partitioning the input state into
cases, specifying for each case what the expected termination kind is. It can be
either:

* ``Normal_Return``, if the subprogram shall return normally,
* ``Exception_Raised``, if it shall raise an (unspecified) exception,
* ``(Exception_Raised => E)``, if it shall raise the exception ``E``, or
* ``Program_Exit``, if it might exit the program abruptly.

As an example, consider the procedure ``Might_Return_Abnormally`` below:

.. literalinclude:: /examples/ug__exit_cases_base/exit_cases.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__exit_cases_base/exit_cases.adb
   :language: ada
   :linenos:

Its contract states that, if it terminates, it shall return normally if ``X`` is
1, raise the exception ``E1`` is ``X`` is 2, raise either ``E1`` or ``E2``,
that is, any exception allowed by its exceptional contract, if ``X`` is 3, and
exit the program abruptly otherwise. The |GNATprove| tool generates verification
conditions to make sure that these restrictions hold. As can be seen below, in
this example, they are all proved.
Note that there are sometimes several checks for a single exit case. For
example here, three verifications are associated to the second case: one to make
sure that the subprogram does not return normally, one to make sure that it does
not exit the program abruptly, and one to check that the expected exception is
propagated on exceptional exit:

.. literalinclude:: /examples/ug__exit_cases_base/test.out
   :language: none

While a check is emitted by |GNATprove| to make sure that the different cases of
an exit cases are disjoint (there shall be no inputs satisfying the guard of
several cases at the same time), it does not ensure that they are complete
(there can be inputs which are not satisfying any guards). In this case, there
are no constraints on how the subprogram is allowed to terminate. As an example,
the contract of ``Might_Return_Abnormally`` would still be proved if the first
and last cases where removed:

.. literalinclude:: /examples/ug__exit_cases_incomplete/exit_cases_incomplete.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__exit_cases_incomplete/exit_cases_incomplete.adb
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__exit_cases_incomplete/test.out
   :language: none

In |SPARK|, as a general rule, postconditions, be they standard, exceptional, or
program exit postconditions, are only enforced if the subprogram terminates.
Exit cases are similar, they do not force the program to terminate but only
ensure that it terminates in the correct way if it does.
As an example, the exit cases contract of ``Might_Return_Abnormally`` is still
verified if its body is replaced by an infinite loop. To enforce termination,
:ref:`Contracts for Termination` should be used in addition to the exit cases.

.. literalinclude:: /examples/ug__exit_cases_non_terminating/exit_cases_non_terminating.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__exit_cases_non_terminating/exit_cases_non_terminating.adb
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__exit_cases_non_terminating/test.out
   :language: none

If an exit cases mentioning ``Program_Exit`` is supplied on a subprogram which
does not have a program exit contract, then by default, |GNATprove| will
assume that it is allowed to terminate the program abruptly. Similarly,
if an exit cases mentioning exceptions is supplied on a subprogram which does
not have an exceptional contract, then by default, |GNATprove| will assume that
it is allowed to propagate the exceptions listed in its exit cases. If some of
these exceptions are unspecified, then it is allowed to propagate any exception.
As an example, |GNATprove| will accept the raise statements and the call to
``OS_Exit`` inside ``Might_Return_Abnormally`` even if we remove its
exceptional and program exit contracts. However,
the default exceptional contract is imprecise in this case, as the propagated
exception is not specified in the last exit case. As a result, when analyzing
a caller like ``Call_Might_Return_Abnormally`` below, the analysis tool won't
know that ``Might_Return_Abnormally`` only propagates ``E1`` or ``E2``:

.. literalinclude:: /examples/ug__exit_cases_default_contract/exit_cases_default_contract.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__exit_cases_default_contract/exit_cases_default_contract.adb
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__exit_cases_default_contract/test.out
   :language: none

.. note::

   Remark that exit cases are always equivalent to a conjunction of standard,
   exceptional, and program exit postconditions, possibly with a number of
   duplicates. As an example, the exit cases of ``Might_Return_Abnormally`` is
   actually equivalent to the combination of normal, exceptional, and program
   exit postconditions below. The postcondition states that
   ``Might_Return_Abnormally`` might only return normally if ``X`` was equal to
   1 before the call. The exceptional contract ensures that exceptions can
   only be propagated if ``X`` was equal to 2 or 3 before the call, and that
   ``E2`` can only be propagated if it was 3. Finally, the program exit
   contracts prevents abrupt termination of the program if ``X`` was 1, 2, or 3:

   .. code-block:: ada

     procedure Might_Return_Abnormally (X : in out Integer) with
       Post => X'Old = 1,
       Exceptional_Cases =>
           (E1 => X'Old in 2 | 3,
            E2 => X'Old = 3),
       Program_Exit => X'Old not in 1 | 2 | 3;

   These alternative contracts are often harder to read though as they involve
   references to the ``Old`` attribute, negations, and duplications.

.. index:: termination; Always_Terminates

Contracts for Termination
-------------------------

*Specific to SPARK*

By default, |GNATprove| verifies termination of all functions
and automatically instantiated lemmas (procedures annotated with
``Automatic_Instantiation``). For procedures or entries, |GNATprove| does not
attempt to verify termination and is only concerned with their partial
correctness. This means that |GNATprove| only verifies that the contract of
each procedure or entry holds whenever it terminates (i.e., returns or raises
an exception). It is still possible that the subprogram does not terminate
in some or all cases (it can for example loop forever or exit the whole program
using ``GNAT.OS_Lib.OS_Exit``).

The ``Always_Terminates`` GNAT specific aspect allows users to request that
|GNATprove| also verifies that a procedure or entry terminates. It is the case
for example of the procedures ``Ok_Terminating`` and ``Bad_Terminating``
below. The aspect can also be used to provide a boolean condition like for the
``Conditionally_Loop`` procedure. If this condition is present, then the proof
of termination is only attempted when the condition evaluates to True on
subprogram entry. As an example, the procedure ``Conditionally_Loop`` might not
terminate if its ``Cond`` parameter evaluates to True, and ``Loop_Forever``
never needs to terminate (but it might):

.. literalinclude:: /examples/ug__possibly_nonterminating/possibly_nonterminating.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__possibly_nonterminating/possibly_nonterminating.adb
   :language: ada
   :linenos:

|GNATprove| verifies the termination of ``OK_Terminating`` and the conditional
termination of ``Conditionally_Loop`` but a failed check is emitted for
``Bad_Terminating`` as it does not terminate.

.. literalinclude:: /examples/ug__possibly_nonterminating/test.out
   :language: none


A package can also be annotated with the ``Always_Terminates`` aspect. It does
not apply to the elaboration of the package, which should always terminate in
|SPARK|, but serves as a default for all the procedures located inside: unless
specified otherwise, a procedure declared inside a package annotated with
``Always_Terminates`` should always terminate.

.. index:: termination; subprogram variant
           recursion; subprogram variant
           Subprogram_Variant

Subprogram Variant
------------------

*Specific to SPARK*

To ensure termination of recursive subprograms, it is possible to annotate them
using the aspect ``Subprogram_Variant``. This aspect provides a value which
should *progress* in some sense between the beginning of the subprogram and each
recursive call. The value is associated to a direction, which can be either
``Increases`` or ``Decreases`` for *numeric* variants, or ``Structural`` for
*structural* variants.

Numeric variants can take a discrete value or, in the
case of the direction ``Decreases``, a big natural (see
``Ada.Numerics.Big_Integers``). On every recursive call, a check is generated
to ensure that the value progresses (decreases or increases) with respect to its
value at the beginning of the subprogram. Since a discrete value is necessarily
bounded by its Ada type, and a big natural is always greater than 0, it is
enough to ensure that there will be no infinite chain of recursive calls.

In the following example, we can verify that the ``Fibonacci`` function
terminates stating that its parameter ``N`` decreases at each recursive call:

.. literalinclude:: /examples/ug__recursive_subprograms/recursive_subprograms.ads
   :language: ada
   :linenos:

|GNATprove| generates one verification condition per recursive call to make sure
that the value given for ``N`` is smaller than the
value of ``N`` on entry of ``Fibonacci``:

.. literalinclude:: /examples/ug__recursive_subprograms/test.out
   :language: none

It is possible to give more than one numeric value in a subprogram variant. In
this case, values are checked in the order in which they appear. If a
value progresses (increases or decreases as specified) then it is enough to
ensure the progression of the whole variant and the subsequent values are not
considered. In the same way, if a value annotated with ``Increases`` actually
decreases strictly (or the other way around) then the evaluation terminates and
the verification of the variant fails. It is only if the values of all the
preceding expressions have been found to be preserved that the subsequent
value is considered. The function ``Max`` computes the index of the maximal
value in a slice of an array. At each recursive call, it shifts the bound
containing the smallest value:

.. literalinclude:: /examples/ug__recursive_subprograms-multiple/recursive_subprograms-multiple.ads
   :language: ada
   :linenos:

The variant specifies that, for each recursive call, either ``F`` increases, or
``F`` stays the same and ``L`` decreases. The order is not important here, as
``L`` and ``F`` are never modified at the same time. This variant can
be verified by |GNATprove|.

.. literalinclude:: /examples/ug__recursive_subprograms-multiple/test.out
   :language: none

Structural variants are generally used on recursive data-structures. The value
associated to such a variant is necessarily a formal parameter of the
subprogram. On every recursive call, a check is generated to ensure that the
actual parameter denoted by the variant designates a strict subcomponent of the
formal parameter denoted the variant at the beggining of the call. Since,
due to the :ref:`Memory Ownership Policy` of |SPARK|, the data-structures cannot
contain cycles, it is enough to ensure that there will be no infinite
chain of recursive calls.

In the following example, we can verify that the ``Length`` function on
singly-linked lists terminates stating that the structure designated by its
parameter ``L`` structurally decreases between two recursive calls:

.. literalinclude:: /examples/ug__recursive_subprograms-structural/recursive_subprograms.ads
   :language: ada
   :linenos:

The fact that the actual parameter for ``L`` on the recursive call designates a
strict subcomponent of the structure designated by formal parameter ``L`` can
be verified by |GNATprove|:

.. literalinclude:: /examples/ug__recursive_subprograms-structural/test.out
   :language: none

Structural variants are subjects to a number of restrictions.
They cannot be combined with other variants, and are checked according to
a mostly syntactic criterion. When these restrictions cannot be followed,
structural variants can be systematically replaced by a decreasing numeric
variant providing the depth (or size) of the data structure, like function
``Length`` above. Strictly speaking, structural variants are only required
to define the function returning that metric.

To verify the termination of mutually recursive subprograms, all subprograms
should be annotated with `compatible` variants. We say that two variants are
compatible if they have the same number of expressions, and matching
values in the list have the same direction and the same base type. For example,
the variants of ``Is_Even`` and ``Is_Odd`` are compatible,
because both are of type ``Integer`` and both decrease.

.. literalinclude:: /examples/ug__recursive_subprograms-mutually/recursive_subprograms-mutually.ads
   :language: ada
   :linenos:

|GNATprove| introduces a check to make sure that the variant progresses at each
mutually recursive call.

.. literalinclude:: /examples/ug__recursive_subprograms-mutually/test.out
   :language: none
