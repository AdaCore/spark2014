.. _How to Write Subprogram Contracts:

How to Write Subprogram Contracts
=================================

|GNATprove| relies on contracts to perform its analysis. User-specified
subprogram contracts are assumed to analyze a subprogram's callers, and
verified when the body of the subprogram is analyzed.

By default, no contracts are compulsory in |GNATprove|. In the absence of
user-provided contracts, |GNATprove| internally generates default
contracts, which may or not be suitable depending on the verification
objective:

* data dependencies (``Global``)

  See :ref:`Generation of Dependency Contracts`. The generated contract may
  be exact when completed from user-specified flow dependencies (Depends),
  or precise when generated from a body in SPARK, or coarse when generated
  from a body in full Ada.

* flow dependencies (``Depends``)

  See :ref:`Generation of Dependency Contracts`. The contract is generated from
  the user-specified or generated data dependencies, by considering that all
  outputs depend on all inputs.

* precondition (``Pre``)

  A default precondition of ``True`` is used in absence of a user-specified
  precondition.

* postcondition (``Post``)

  A default postcondition of ``True`` is used in absence of a user-specified
  postcondition, except for expression functions. For the latter, the body of
  the expression function is used to generate a matching postcondition. See
  :ref:`Expression Functions`.

Knowing which contracts to write depends on the specific verification
objectives to achieve.

.. _Generation of Dependency Contracts:

Generation of Dependency Contracts
----------------------------------

By default, |GNATprove| does not require the user to write data dependencies
(introduced with aspect ``Global``) and flow dependencies (introduced
with aspect ``Depends``), as it can automatically generate them from the
program.

This behavior can be disabled using the ``--no-global-generation`` switch,
which means a missing data dependency is the same as ``Global => null``.
Note that this option also forces ``--no-inlining`` (see :ref:`Contextual
Analysis of Subprograms Without Contracts`).

.. note::

   |GNATprove| does not generate warning or check messages when the body of a
   subprogram does not respect a generated contract. Indeed, the generated
   contract is a safe over-approximation of the real contract, hence it is
   unlikely that the subprogram body respects it. The generated contract is
   used instead to verify proper initialization and respect of dependency
   contracts in the callers of the subprogram.

.. note::

   Intrinsic subprograms such as arithmetic operations, and shift/rotate
   functions without user-provided functional contracts (precondition,
   postcondition or contract cases) are handled specially by |GNATprove|.

.. note::

   The ``--no-global-generation`` switch makes |GNATprove| behave more like
   the previous SPARK 2005 tools, which makes this switch attractive
   for project trying to migrate to the new |GNATprove| tools, or for
   projects that maintain dual annotations.

.. _Auto Completion for Incomplete Contracts:

Auto Completion for Incomplete Contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When only the data dependencies (resp. only the flow dependencies) are given on
a subprogram, |GNATprove| completes automatically the subprogram contract with
the matching flow dependencies (resp. data dependencies).

Writing Only the Data Dependencies
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When only the data dependencies are given on a subprogram, |GNATprove|
completes them with flow dependencies that have all outputs depending on all
inputs. This is a safe over-approximation of the real contract of the
subprogram, which allows to detect all possible errors of initialization and
contract violation in the subprogram and its callers, but which may also lead
to false alarms because it is imprecise.

Take for example procedures ``Add`` and ``Swap`` for which data dependencies
are given, but no flow dependencies:

.. literalinclude:: /gnatprove_by_example/examples/only_data_dependencies.ads
   :language: ada
   :linenos:

|GNATprove| completes the contract of ``Add`` and ``Swap`` with flow
dependencies that are equivalent to:

.. code-block:: ada

   procedure Add (X : Integer) with
     Global  => (In_Out => V),
     Depends => (V =>+ X);

   procedure Swap (X : in out Integer) with
     Global  => (In_Out => V),
     Depends => ((X, V) => (X, V));

Other flow dependencies with fewer dependencies between inputs and outputs
would be compatible with the given data dependencies of ``Add`` and
``Swap``. |GNATprove| chooses the contracts with the most dependencies. Here,
this corresponds to the actual contract for ``Add``, but to an imprecise
contract for ``Swap``:

.. literalinclude:: /gnatprove_by_example/examples/only_data_dependencies.adb
   :language: ada
   :linenos:

This results in false alarms when |GNATprove| verifies the dependency contract
of procedure ``Call_Swap`` which calls ``Swap``, while it succeeds in verifying
the dependency contract of ``Call_Add`` which calls ``Add``:

.. literalinclude:: /gnatprove_by_example/results/only_data_dependencies.flow
   :language: none

The most precise dependency contract for ``Swap`` would be:

.. code-block:: ada

   procedure Swap (X : in out Integer) with
     Global  => (In_Out => V),
     Depends => (V => X, X => V);

If you add this precise contract in the program, then |GNATprove| can also
verify the dependency contract of ``Call_Swap``.

Note that the generated dependency contracts are used in the analysis of
callers, but |GNATprove| generates no warnings or check messages if the body of
``Add`` or ``Swap`` have fewer flow dependencies, as seen above. That's a
difference between these contracts being present in the code or auto completed.

Writing Only the Flow Dependencies
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When only the flow dependencies are given on a subprogram, |GNATprove|
completes it with the only compatible data dependencies.

Take for example procedures ``Add`` and ``Swap`` as previously, expect now flow
dependencies are given, but no data dependencies:

.. literalinclude:: /gnatprove_by_example/examples/only_flow_dependencies.ads
   :language: ada
   :linenos:

The body of the unit is the same as before:

.. literalinclude:: /gnatprove_by_example/examples/only_flow_dependencies.adb
   :language: ada
   :linenos:

|GNATprove| verifies the data and flow dependencies of all
subprograms, including ``Call_Add`` and ``Call_Swap``, based on the completed
contracts for ``Add`` and ``Swap``.

Precise Generation for |SPARK| Subprograms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When no data or flow dependencies are given on a |SPARK| subprogram,
|GNATprove| generates precise data and flow dependencies by using
path-sensitive flow analysis to track data flows in the subprogram body:

 * if a variable is written completely on all paths in a subprogram body, it is
   considered an output of the subprogram; and
 * other variables that are written in a subprogram body are considered both
   inputs and outputs of the subprogram (even if they are not read explicitly,
   their output value may depend on their input value); and
 * if a variable is only read in a subprogram body, it is considered an input
   of the subprogram; and
 * all outputs are considered to potentially depend on all inputs.

Case 1: No State Abstraction
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Take for example a procedure ``Set_Global`` without contract which initializes
a global variable ``V`` and is called in a number of contexts:

.. literalinclude:: /gnatprove_by_example/examples/gen_global.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/gen_global.adb
   :language: ada
   :linenos:

|GNATprove| generates data and flow dependencies for procedure
``Set_Global`` that are equivalent to:

.. code-block:: ada

   procedure Set_Global with
     Global  => (Output => V),
     Depends => (V => null);

Note that the above contract would be illegal as given, because it refers to
global variable ``V`` which is not visible at the point where ``Set_Global`` is
declared in ``gen_global.ads``. Instead, a user who would like to write this
contract on ``Set_Global`` would have to use abstract state.

That generated contract for ``Set_Global`` allows |GNATprove| to both detect
possible errors when calling ``Set_Global`` and to verify contracts given by
the user on callers of ``Set_Global``. For example, procedure
``Set_Global_Twice`` calls ``Set_Global`` twice in a row, which makes the first
call useless as the value written in ``V`` is immediately overwritten by the
second call. This is detected by |GNATprove|, which issues two warnings on
line 18:

.. literalinclude:: /gnatprove_by_example/results/gen_global.flow
   :language: none

Note that |GNATprove| also issues a warning on subprogram ``Do_Nothing`` which
has no effect, while it correctly analyzes that ``Set_Global`` has an effect,
even if it has the same signature with no contract as ``Do_Nothing``.

|GNATprove| also uses the generated contract for ``Set_Global`` to analyze
procedure ``Set_Global_Conditionally``, which allows it to verify the contract
given by the user for ``Set_Global_Conditionally``:

.. code-block:: ada

   procedure Set_Global_Conditionally (X : Boolean) with
     Global  => (Output => V),
     Depends => (V => X)

Case 2: State Abstraction Without Dependencies
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If an abstract state (see :ref:`State Abstraction`)
is declared by the user but no dependencies are specified on
subprogram declarations, then |GNATprove| generates data and flow dependencies
which take abstract state into account.

For example, take unit ``Gen_Global`` previously seen, where an abstract state
``State`` is defined for package ``Gen_Abstract_Global``, and refined into
global variable ``V`` in the body of the package:

.. literalinclude:: /gnatprove_by_example/examples/gen_abstract_global.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/gen_abstract_global.adb
   :language: ada
   :linenos:

We have chosen here to declare procedure ``Set_Global_Conditionally`` in
``gen_abstract_global.ads``, and so to express its user contract abstractly. We
could also have kept it local to the unit.

|GNATprove| gives the same results on this unit as before: it issues warnings
for the possible error in ``Set_Global_Twice`` and it verifies the contract
given by the user for ``Set_Global_Conditionally``:

.. literalinclude:: /gnatprove_by_example/results/gen_abstract_global.flow
   :language: none

Case 3: State Abstraction Without Refined Dependencies
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If abstract state is declared by the user and abstract dependencies are
specified on subprogram declarations, but no refined dependencies are specified
on subprogram implementations (as described :ref:`State Abstraction and
Dependencies`), then |GNATprove| generates refined data and flow dependencies
for subprogram implementations.

For example, take unit ``Gen_Abstract_Global`` previously seen, where only
abstract data and flow dependencies are specified:

.. literalinclude:: /gnatprove_by_example/examples/gen_refined_global.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/gen_refined_global.adb
   :language: ada
   :linenos:

|GNATprove| gives the same results on this unit as before: it issues warnings
for the possible error in ``Set_Global_Twice`` and it verifies the contract
given by the user for ``Set_Global_Conditionally``:

.. literalinclude:: /gnatprove_by_example/results/gen_refined_global.flow
   :language: none

Note that although abstract and refined dependencies are the same here, this is
not always the case, and |GNATprove| will use the more precise generated
dependencies to analyze calls to subprograms inside the unit.

.. _Coarse Generation for non-SPARK Subprograms:

Coarse Generation for non-|SPARK| Subprograms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When no data or flow dependencies are given on a non-|SPARK| subprogram,
|GNATprove| generates coarser data and flow dependencies based on the
reads and writes to variables in the subprogram body:

 * if a variable is written in a subprogram body, it is considered both an
   input and an output of the subprogram; and
 * if a variable is only read in a subprogram body, it is considered an input
   of the subprogram; and
 * all outputs are considered to potentially depend on all inputs.

For example, take unit ``Gen_Global`` previously seen, where the body of
``Set_Global`` is marked with ``SPARK_Mode => Off``:

.. literalinclude:: /gnatprove_by_example/examples/gen_ada_global.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/gen_ada_global.adb
   :language: ada
   :linenos:

|GNATprove| generates a data and flow dependencies for procedure
``Set_Global`` that are equivalent to:

.. code-block:: ada

   procedure Set_Global with
     Global  => (In_Out => V),
     Depends => (V => V);

This is a safe over-approximation of the real contract for
``Set_Global``, which allows to detect all possible errors of initialization
and contract violation in ``Set_Global`` callers, but which may also lead to
false alarms because it is imprecise. Here, |GNATprove| generates a wrong
high message that the call to ``Set_Global`` on line 25 reads an uninitialized value
for ``V``:

.. literalinclude:: /gnatprove_by_example/results/gen_ada_global.flow
   :language: none

This is because the generated contract for ``Set_Global`` is not precise
enough, and considers ``V`` as an input of the procedure. Even if the body of
``Set_Global`` is not in |SPARK|, the user can easily provide the precise
information to |GNATprove| by adding a suitable contract to ``Set_Global``,
which requires to define an abstract state ``State`` like in the previous
section:

.. code-block:: ada

   procedure Set_Global with
     Global  => (Output => State),
     Depends => (State => null);

With such a user contract on ``Set_Global``, |GNATprove| can verify the
contract of ``Set_Global_Conditionally`` without false alarms.

Writing Dependency Contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Since |GNATprove| generates data and flow dependencies, you don't need
in general to add such contracts if you don't want to.

The main reason to add such contracts is when you want |GNATprove| to verify
that the implementation respects specified data dependencies and flow
dependencies. For those projects submitted to certification, verification of
data coupling and input/output relations may be a required verification
objective, which can be achieved automatically with |GNATprove| provided the
specifications are written as contracts.

Even if you write dependency contracts for the publicly
visible subprograms, which describe the services offered by the unit, there is
no need to write similar contracts on internal subprograms defined in the unit
body. |GNATprove| can generate data and flow dependencies on these.

Also, as seen in the previous section, the data and flow dependencies
generated by |GNATprove| may be imprecise, in which case it is necessary to add
manual contracts to avoid false alarms.

.. _Writing Contracts for Program Integrity:

Writing Contracts for Program Integrity
---------------------------------------

The most common use of contracts is to ensure program integrity, that is, the
program keeps running within safe boundaries. For example, this includes the
fact that the control flow of the program cannot be circumvented (e.g. through
a buffer overflow vulnerability) and that data is not corrupted (e.g. data
invariants are preserved).

Preconditions can be written to ensure program integrity, and in particular
they ensure:

* absence of run-time errors (AoRTE): no violations of language rules which
  would lead to raising an exception at run time (preconditions added to all
  subprograms which may raise a run-time error); and
* defensive programming: no execution of a subprogram from an unexpected state
  (preconditions added to subprograms in the public API, to guard against
  possible misuse by client units); and
* support of maintenance: prevent decrease in integrity (regressions, code rot)
  introduced during program evolution (preconditions added to internal
  subprograms, to guard against violations of the conditions to call these
  subprograms inside the unit itself); and
* invariant checking: ensure key data invariants are maintained throughout
  execution (preconditions added to all subprograms which may break the
  invariant).

For example, unit ``Integrity`` contains examples of all four kinds of
preconditions:

* Precondition ``X >= 0`` on procedure ``Seen_One`` ensures AoRTE, as otherwise
  a negative value for ``X`` would cause the call to ``Update`` to fail a range
  check, as ``Update`` expects a non-negative value for its parameter.
* Precondition ``X < Y`` on procedure ``Seen_Two`` ensures defensive
  programming, as the logic of the procedure is only correctly updating global
  variables ``Max1`` and ``Max2`` to the two maximal values seen if parameters
  ``X`` and ``Y`` are given in strictly increasing order.
* Precondition ``X > Max2`` on procedure ``Update`` ensures support of
  maintenance, as this internal procedure relies on this condition on its
  parameter to operate properly.
* Precondition ``Invariant`` on procedure ``Update`` ensures invariant
  checking, as the property that ``Max2`` is less than ``Max1`` expressed in
  ``Invariant`` should be always respected.

.. literalinclude:: /gnatprove_by_example/examples/integrity.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/integrity.adb
   :language: ada
   :linenos:

Note that ``pragma Assertion_Policy (Pre => Check)`` in ``integrity.ads``
ensures that the preconditions on the public procedures ``Seen_One`` and
``Seen_Two`` are always enabled at run time, while the precondition on internal
subprogram ``Update`` is only enabled at run time if compiled with switch
``-gnata`` (typically set only for debugging or testing). |GNATprove| always
takes contracts into account, whatever value of ``Assertion_Policy``.

|GNATprove| cannot verify that all preconditions on ``Integrity`` are
respected. Namely, it cannot verify that the call to ``Update`` inside
``Seen_One`` respects its precondition, as it is not known from the calling
context that ``Invariant`` holds:

.. literalinclude:: /gnatprove_by_example/results/integrity.prove
   :language: none

Note that, although ``Invariant`` is not required to hold either on entry to
``Seen_Two``, the tests performed in if-statements in the body of ``Seen_Two``
ensure that ``Invariant`` holds when calling ``Update`` inside ``Seen_Two``.

To prove completely the integrity of unit ``Integrity``, it is sufficient to
add ``Invariant`` as a precondition and postcondition on every subprogram which
modifies the value of global variables ``Max1`` and ``Max2``:

.. literalinclude:: /gnatprove_by_example/examples/integrity_proved.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/integrity_proved.adb
   :language: ada
   :linenos:

Here is the result of running |GNATprove|:

.. literalinclude:: /gnatprove_by_example/results/integrity_proved.prove
   :language: none

.. _Writing Contracts for Functional Correctness:

Writing Contracts for Functional Correctness
--------------------------------------------

Going beyond program integrity, it is possible to express functional properties
of the program as subprogram contracts. Such a contract can express either
partially or completely the behavior of the subprogram. Typical simple
functional properties express the range/constraints for parameters on entry and
exit of subprograms (encoding their `type-state`), and the state of the
module/program on entry and exit of subprograms (encoding a safety or security
automaton). For those projects submitted to certification, expressing a
subprogram requirement or specification as a complete functional contract
allows |GNATprove| to verify automatically the implementation against the
requirement/specification.

For example, unit ``Functional`` is the same as ``Integrity_Proved`` seen
previously, with additional functional contracts:

* The postcondition on procedure ``Update`` (expressed as a ``Post`` aspect) is
  a complete functional description of the behavior of the subprogram. Note the
  use of an if-expression.
* The postcondition on procedure ``Seen_Two`` (expressed as a ``Post`` aspect)
  is a partial functional description of the behavior of the subprogram.
* The postcondition on procedure ``Seen_One`` (expressed as a
  ``Contract_Cases`` aspect) is a complete functional description of the
  behavior of the subprogram. There are three cases which correspond to
  different possible behaviors depending on the values of parameter ``X`` and
  global variables ``Max1`` and ``Max2``. The benefit of expressing the
  postcondition as contract cases is both the gain in readability (no need to
  use ``'Old`` for the guards, as in the postcondition of ``Update``) and the
  automatic verification that the cases are disjoint and complete.

Note that global variables ``Max1`` and ``Max2`` are referred to through public
accessor functions ``Max_Value_Seen`` and ``Second_Max_Value_Seen``. These
accessor functions can be declared after the contracts in which they appear, as
contracts are semantically analyzed only at the end of package declaration.

.. literalinclude:: /gnatprove_by_example/examples/functional.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/functional.adb
   :language: ada
   :linenos:

|GNATprove| manages to prove automatically almost all of these functional
contracts, except for the postcondition of ``Seen_Two`` (note in particular the
proof that the contract cases for ``Seen_One`` on line 10 are disjoint and
complete):

.. literalinclude:: /gnatprove_by_example/results/functional.prove
   :language: none

The counterexample displayed for the postcondition not proved corresponds to a
case where ``Max1 = Max2 = 2`` on entry to procedure ``Seen_Two``. By
highlighting the path for the counterexample in GPS (see :ref:`Running
GNATprove from GPS`), the values of parameters for this counterexample are also
displayed, here ``X = 0`` and ``Y = 1``. With these values, ``Max1`` and ``Max2``
would still be equal to 2 on exit, thus violating the part of the postcondition
stating that ``Max_Value_Seen /= Second_Max_Value_Seen``.

Another way to see it is to run |GNATprove| in mode ``per_path`` (see
:ref:`Running GNATprove from the Command Line` or :ref:`Running GNATprove from
GPS`), and highlight the path on which the postcondition is not proved, which
shows that when the last branch of the if-statement is taken, the following
property is not proved::

  functional.ads:31:14: medium: postcondition might fail, cannot prove Max_Value_Seen /= (Second_Max_Value_Seen)

The missing piece of information here is that ``Max1`` and ``Max2`` are never
equal, except when they are both zero (the initial value). This can be added to
function ``Invariant`` as follows:

.. literalinclude:: /gnatprove_by_example/examples/functional_proved.adb
   :language: ada
   :lines: 7-8

With this more precise definition for ``Invariant``, all contracts are now
proved by |GNATprove|:

.. literalinclude:: /gnatprove_by_example/results/functional_proved.prove
   :language: none

In general, it may be needed to further refine the preconditions of subprograms
to be able to prove their functional postconditions, to express either specific
constraints on their calling context, or invariants maintained throughout the
execution.

.. _Writing Contracts on Main Programs:

Writing Contracts on Main Programs
----------------------------------

Parameterless procedures and parameterless functions with Integer return type,
that are in their own compilation unit, are identified by |GNATprove| as
potential main subprograms. These subprograms are special because they can
serve as an entry point to the program. If a main subprogram has a
precondition, SPARK will generate a check that this precondition holds at the
beginning of the execution of the main program, assuming the
``Initial_Condition`` aspects of all with'ed packages.

Note that apart from this additional check, main subprograms behave like any
other subprogram. They can be called from anywhere, and their preconditions
need to be checked when they are called.

.. _Writing Contracts on Imported Subprograms:

Writing Contracts on Imported Subprograms
-----------------------------------------

Contracts are particularly useful to specify the behavior of imported
subprograms, which cannot be analyzed by |GNATprove|. It is compulsory to
specify in data dependencies the global variables these imported subprograms
may read and/or write, otherwise |GNATprove| assumes ``null`` data dependencies
(no global variable read or written).

.. note::

   A subprogram whose implementation is not available to |GNATprove|, either
   because the corresponding unit body has not been developed yet, or because
   the unit body is not part of the files analyzed by |GNATprove| (see
   :ref:`Specifying Files To Analyze` and :ref:`Excluding Files From
   Analysis`), is treated by |GNATprove| like an imported subprogram.

.. note::

   Intrinsic subprograms such as arithmetic operations and shift/rotate
   functions are handled specially by GNATprove. Except for shift/rotate
   operations with a user-provided functional contract (precondition,
   postcondition or contract cases) which are treated like regular functions.

For example, unit ``Gen_Imported_Global`` is a modified version of the
``Gen_Abstract_Global`` unit seen previously in :ref:`Generation of Dependency
Contracts`, where procedure ``Set_Global`` is imported from C:

.. literalinclude:: /gnatprove_by_example/examples/gen_imported_global.ads
   :language: ada
   :linenos:

Note that we added data dependencies to procedure ``Set_Global``, which can
be used to analyze its callers. We did not add flow dependencies, as
they are the same as the auto completed ones (see :ref:`Auto Completion for
Incomplete Contracts`).

.. literalinclude:: /gnatprove_by_example/examples/gen_imported_global.adb
   :language: ada
   :linenos:

Note that we added an ``Address`` aspect to global variable ``V``, so that it
can be read/written from a C file.

|GNATprove| gives the same results on this unit as before: it issues warnings
for the possible error in ``Set_Global_Twice`` and it verifies the contract
given by the user for ``Set_Global_Conditionally``:

.. literalinclude:: /gnatprove_by_example/results/gen_imported_global.flow
   :language: none

It is also possible to add functional contracts on imported subprograms, which
|GNATprove| uses to prove properties of their callers.  It is compulsory to
specify in a precondition the conditions for calling these imported subprograms
without errors, otherwise |GNATprove| assumes a default precondition of
``True`` (no constraints on the calling context). One benefit of these
contracts is that they are verified at run time when the corresponding
assertion is enabled in Ada (either with pragma ``Assertion_Policy`` or
compilation switch ``-gnata``).

.. note::

   A subprogram whose implementation is not in |SPARK| is treated by
   |GNATprove| almost like an imported subprogram, except that coarse data and
   flow dependencies are generated (see :ref:`Coarse Generation for non-SPARK
   Subprograms`). In particular, unless the user adds a precondition to such a
   subprogram, |GNATprove| assumes a default precondition of ``True``.

For example, unit ``Functional_Imported`` is a modified version of the
``Functional_Proved`` unit seen previously in :ref:`Writing Contracts for
Functional Correctness`, where procedures ``Update`` and ``Seen_One`` are
imported from C:

.. literalinclude:: /gnatprove_by_example/examples/functional_imported.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/functional_imported.adb
   :language: ada
   :linenos:

Note that we added data dependencies to the imported procedures, as
|GNATprove| would assume otherwise incorrectly ``null`` data dependencies.

As before, all contracts are proved by |GNATprove|:

.. literalinclude:: /gnatprove_by_example/results/functional_imported.prove
   :language: none

.. _Contextual Analysis of Subprograms Without Contracts:

Contextual Analysis of Subprograms Without Contracts
----------------------------------------------------

It may be convenient to create local subprograms without necessarily specifying
a contract for these. |GNATprove| attempts to perform a contextual analysis of
these local subprograms without contract, at each call site, as if the code of
the subprograms was inlined. Thus, the analysis proceeds in that case as if it
had the most precise contract for the local subprogram, in the context of its
calls.

Let's consider as previously a subprogram which adds two to its integer input:

.. literalinclude:: /gnatprove_by_example/examples/arith_with_local_subp.ads
   :language: ada
   :linenos:

And let's implement it by calling two local subprograms without contracts
(which may or not have a separate declaration), which each increment the input
by one:

.. literalinclude:: /gnatprove_by_example/examples/arith_with_local_subp.adb
   :language: ada
   :linenos:

|GNATprove| would not be able to prove that the addition in
``Increment_In_Body`` or ``Increment_Nested`` cannot overflow in any
context. If it was using only the default contract for these subprograms, it
also would not prove that the contract of ``Add_Two`` is respected.  But since
it analyzes these subprograms in the context of their calls only, it proves
here that no overflow is possible, and that the two increments correctly
implement the contract of ``Add_Two``:

.. literalinclude:: /gnatprove_by_example/results/arith_with_local_subp.prove
   :language: none
   :linenos:

This contextual analysis is available only for regular functions (not
expression functions) or procedures that are not externally visible (not
declared in the public part of the unit), without contracts (any of Global,
Depends, Pre, Post, Contract_Cases), and respect the following conditions:

 * does not contain nested subprogram or package declarations or instantiations
 * not recursive
 * not a generic instance
 * not defined in a generic instance
 * has a single point of return at the end of the subprogram
 * not called in an assertion or a contract
 * not called in a potentially unevaluated context
 * not called before its body is seen

If any of the above conditions is violated, |GNATprove| issues a warning to
explain why the subprogram could not be analyzed in the context of its calls,
and then proceeds to analyze it normally, using the default
contract. Otherwise, both flow analysis and proof are done for the subprogram
in the context of its calls.

Note that it is very simple to prevent contextual analysis of a local
subprogram, by adding a contract to it, for example a simple ``Pre => True`` or
``Global => null``. To prevent contextual analysis of all subprograms, pass the
switch ``--no-inlining`` to |GNATprove|. This may be convenient during
development if the ultimate goal is to add contracts to subprograms to analyze
them separately, as contextual analysis may cause the analysis to take much
more time and memory.

.. _Subprogram Termination:

Subprogram Termination
----------------------

|GNATprove| is only concerned with partial correctness of subprograms, that is,
it only checks that the contract of a subprogram holds when it terminates
normally. What is more, |GNATprove| will enforce that no exception will be
raised at runtime. Together, these two points ensure that every |SPARK|
subprogram formally verified using GNATprove will always return normally in a
state that respects its postcondition, as long as it terminates.

In general, |GNATprove| does not attempt to verify termination of subprograms.
It can be instructed to do so using a |GNATprove| specific Annotate pragma. On
the following example, we instruct |GNATprove| that the five ``F`` functions
should terminate:

.. literalinclude:: /gnatprove_by_example/examples/terminating_annotations.ads
   :language: ada
   :linenos:

If every subprogram in a package is terminating, the package itself can be
annotated with the terminating annotation. If the annotation is located on a
generic package, then it should be valid for every instance of the package.

An aspect can be used instead of a pragma for both packages and subprograms:

.. code-block:: ada

   package Pack with
      Annotate => (GNATprove, Terminating)
   is
      procedure Proc with
        Annotate => (GNATprove, Terminating);
   ...

If a subprogram in |SPARK| is explicitly annotated as terminating, flow analysis
will attempt to make sure that all the paths through the subprogram effectively
return. In effect, it will look for while loops with no loop variants, recursive
calls and calls to subprograms which are not known to be terminating. If
|GNATprove| cannot make sure that the annotated subprogram is always
terminating, it will then emit a failed check. As an example, let us consider
the following implementation of the five ``F`` functions:

.. literalinclude:: /gnatprove_by_example/examples/terminating_annotations.adb
   :language: ada
   :linenos:

As can be easily verified by review, all these functions terminate, and all
return 0. As can be seen below, |GNATprove| will fail to verify that ``F_Rec``,
``F_While``, and ``F_Call`` terminate.

.. literalinclude:: /gnatprove_by_example/results/terminating_annotations.flow
   :language: none
   :linenos:

Let us look at each function to understand what happens. The function ``F_Rec``
is recursive, and the function ``F_While`` contains a while loop. Both cases
can theoretically lead to an infinite path in the subprogram, which is why
GNATprove cannot verify that they terminate. |GNATprove| does not complain
about not being able to verify the termination of ``F_Not_SPARK``. Clearly, it
is not because it could verify it, as it contains exactly the same loop as
``F_While``. It is because, as the body of ``F_Not_SPARK`` has been excluded
from analysis using ``SPARK_Mode => Off``, |GNATprove| does not attempt to
prove that it terminates.  When looking at the body of ``F_Call``, we can see
that it calls a procedure ``Not_SPARK``. Clearly, this procedure is
terminating, as it does not do anything. But, as the body of ``No_SPARK`` has
been hidden from analysis using ``SPARK_Mode => Off``, |GNATprove| cannot
deduce that it terminates. As a result, it stays in the safe side, and assumes
that ``Not_SPARK`` could loop, which causes the verification of ``F_Call`` to
fail. Finally, |GNATprove| is able to verify that ``F_Term`` terminates, though
it contains a while loop.  Indeed, the number of possible iterations of the
loop has been bounded using a ``Loop_Variant``. Also note that, though it was
not able to prove termination of ``F_Rec``, ``F_While``, and ``F_Call``,
GNATprove will still trust the annotation and consider them as terminating when
verifying ``F_Term``.

.. note::

   Possible nontermination of a subprogram may influence |GNATprove| proof
   capabilities. Indeed, to avoid soundness issues due to nontermination in
   logical formulas, GNATprove will not be able to see the contract of
   nonterminating functions if they are called from definitions of constants,
   from contracts, or from assertions. In such a case, an information message
   will be emitted, stating that (implicit) contracts of the function are not
   available for proof. This message won't appear if a ``Terminating``
   annotation is supplied for the function as explained above.
