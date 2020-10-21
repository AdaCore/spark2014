.. _Subprogram Contracts:

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
  precondition and a postcondition.
* The `data dependencies` introduced by aspect ``Global`` specify the global
  data read and written by the subprogram.
* The `flow dependencies` introduced by aspect ``Depends`` specify how
  subprogram outputs depend on subprogram inputs.
* The `subprogram variant` introduced by aspect ``Subprogram_Variant`` is
  used to ensure termination of recursive subprograms.

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

.. _Subprogram Variant:

Subprogram Variant
------------------

[|SPARK|]

To ensure termination of recursive subprograms, it is possible to annotate them
using the aspect ``Subprogram_Variant``. This aspect provides a discrete
value along with a direction (``Increases`` or ``Decreases``). On every
recursive call, a check is generated to ensure that the discrete value progresses
(decreases or increases) with respect to its value at the beginning of the
subprogram. Since a discrete value is necessarily bounded by its Ada type, it
is enough to ensure that there will be no infinite chain of recursive calls.
In the following example, we can verify that the ``Fibonacci`` function
terminates stating that its parameter ``N`` decreases at each recursive call:

.. literalinclude:: /examples/tests/recursive_subprograms/recursive_subprograms.ads
   :language: ada
   :linenos:

|GNATprove| generates one verification condition per recursive call to make sure
that the value given for ``N`` is smaller than the
value of ``N`` on entry of ``Fibonacci``:

.. literalinclude:: /examples/tests/recursive_subprograms/test.out
   :language: none

It is possible to give more than one discrete value in a subprogram variant. In
this case, values are checked in the order in which they appear. If a
value progresses (increases or decreases as specified) then it is enough to
ensure the progression of the whole variant and the subsequent values are not
considered. In the same way, if a value annotated with ``Increases`` actually
decreases strictly (or the other way around) then the evaluation terminates and
the verification of the variant fails. It is only if the values of all the
preceding discrete expressions have been found to be preserved that the subsequent
value is considered. The function ``Max`` computes the index of the maximal
value in a slice of an array. At each recursive call, it shifts the bound
containing the smallest value:

.. literalinclude:: /examples/tests/recursive_subprograms-multiple/recursive_subprograms-multiple.ads
   :language: ada
   :linenos:

The variant specifies that, for each recursive call, either ``F`` increases, or
``F`` stays the same and ``L`` decreases. The order is not important here, as
``L`` and ``F`` are never modified at the same time. This variant can
be verified by |GNATprove|.

.. literalinclude:: /examples/tests/recursive_subprograms-multiple/test.out
   :language: none

To verify the termination of mutually recursive subprograms, all subprograms
should be annotated with `compatible` variants. We say that two variants are
compatible if they have the same number of discrete expressions, and matching
values in the list have the same direction and the same base type. For example,
the variants of ``Is_Even`` and ``Is_Odd`` are compatible,
because both are of type ``Integer`` and both decrease.

.. literalinclude:: /examples/tests/recursive_subprograms-mutually/recursive_subprograms-mutually.ads
   :language: ada
   :linenos:

|GNATprove| introduces a check to make sure that the variant progresses at each
mutually recursive call.

.. literalinclude:: /examples/tests/recursive_subprograms-mutually/test.out
   :language: none
