.. _basic_examples:

Basic Examples
--------------

The examples in this section have no loops, and do not use more complex
features of |SPARK| like :ref:`Ghost Code`, :ref:`Interfaces to the Physical
World`, or :ref:`Object Oriented Programming and Liskov Substitution
Principle`.

.. _Increment:

Increment
^^^^^^^^^

Consider a simple procedure that increments its integer parameter ``X``:

.. literalinclude:: examples/increment.adb
   :language: ada
   :linenos:

As this procedure does not have a contract yet, |GNATprove| only checks that
there are no possible reads of uninitialized data and no possible run-time
errors in the procedure. Here, it issues a message about a possible overflow
check failure on ``X + 1``:

.. literalinclude:: results/increment.prove
   :language: none

The counterexample displayed tells us that ``Increment`` could be called on
value ``Integer'Last`` for parameter ``X``, which would cause the increment to
raise a run-time error. As suggested by the possible explanation in the message
issued by |GNATprove|, one way to eliminate this vulnerability is to add a
precondition to ``Increment`` specifying that ``X`` should be less than
``Integer'Last`` when calling the procedure:

.. literalinclude:: examples/increment_guarded.adb
   :language: ada
   :linenos:

As this procedure has a contract now, |GNATprove| checks like before that there
are no possible reads of uninitialized data and no possible run-time errors in
the procedure, including in its contrat, and that the procedure implements its
contract. As expected, |GNATprove| now proves that there is no possible
overflow check failure on ``X + 1``:

.. literalinclude:: results/increment_guarded.prove
   :language: none

The precondition is usually the first contract added to a subprogram, but there
are other :ref:`Subprogram Contracts`. Here is a version of ``Increment``
with:

* global dependencies (aspect ``Global``) stating that the procedure reads and
  writes no global variables
* flow dependencies (aspect ``Depends``) stating that the final value of
  parameter ``X`` only depends on its input value
* a precondition (aspect ``Pre``) stating that parameter ``X`` should be less
  than ``Integer'Last`` on entry
* a postcondition (aspect ``Post``) stating that parameter ``X`` should have
  been incremented by the procedure on exit

.. literalinclude:: examples/increment_full.adb
   :language: ada
   :linenos:

|GNATprove| checks that ``Increment_Full`` implements its contract, and that it
cannot raise run-time errors or read uninitialized data. By default,
|GNATprove|'s output is empty in such a case, but we can request that it prints
one line per check proved by using switch ``--report=all``, which we do here:

.. literalinclude:: results/increment_full.prove
   :language: none

As subprogram contracts are used to analyze callers of a subprogram, let's
consider a procedure ``Increment_Calls`` that calls the different versions of
``Increment`` presented so far:

.. literalinclude:: examples/increment_calls.adb
   :language: ada
   :linenos:

|GNATprove| proves all preconditions expect the one on the second call to
``Increment_Guarded``:

.. literalinclude:: results/increment_calls.prove
   :language: none

``Increment`` has no precondition, so there is nothing to check here except the
initialization of ``X`` when calling ``Increment`` on lines 11 and 12. But
remember that |GNATprove| did issue a message about a true vulnaribility on
``Increment``'s implementation.

This vulnerability was corrected by adding a precondition to
``Increment_Guarded``. This has the effect of pushing the constraint on
callers, here procedure ``Increment_Calls``. As expected, |GNATprove| proves
that the first call to ``Increment_Guarded`` on line 15 satisfies its
precondition. But it does not prove the same for the second call to
``Increment_Guarded`` on line 16, because the value of ``X`` on line 16 was set
by the call to ``Increment_Guarded`` on line 15, and the contract of
``Increment_Guarded`` does not say anything about the possible values of ``X``
on exit.

As suggested by the possible explanation in the message issued by |GNATprove|,
a postcondition like the one on ``Increment_Full`` is needed so that
|GNATprove| can check the second call to increment ``X``. As expected,
|GNATprove| proves that both calls to ``Increment_Full`` on lines 19 and 20
satisfy their precondition.

In some cases, the user is not interested in specifying and verifying a
complete contract like the one on ``Increment_Full``, typically for helper
subprograms defined locally in a subprogram or package body. |GNATprove| allows
performing :ref:`Contextual Analysis of Subprograms Without Contracts` for these
local subprograms. For example, consider a local definition of ``Increment``
inside procedure ``Increment_Local``:

.. literalinclude:: examples/increment_local.adb
   :language: ada
   :linenos:

Although ``Increment`` has no contract (like the previous non-local version),
|GNATprove| proves that this program is free from run-time errors, and that the
assertion on line 15 holds:

.. literalinclude:: results/increment_local.prove
   :language: none

.. _Swap:

Swap
^^^^

Consider a simple procedure that swaps its integer parameters ``X`` and ``Y``,
whose simple-minded implementation is wrong:

.. literalinclude:: examples/swap_bad.adb
   :language: ada
   :linenos:

As this procedure does not have a contract yet, |GNATprove| only checks that
there are no possible reads of uninitialized data and no possible run-time
errors in the procedure. Here, it simply issues a warning:

.. literalinclude:: results/swap_bad.flow
   :language: none

But we know the procedure is wrong, so we'd like to get an error of some sort!
We could not detect it with |GNATprove| because the error is functional, and
|GNATprove| cannot guess the intended functionality of
``Swap_Bad``. Fortunately, we can give this information to |GNATprove| by
adding a contract to ``Swap_Bad``.

One such contract is the flow dependencies introduced by aspect
``Depends``. Here it specifies that the final value of ``X`` (resp. ``Y``)
should depend on the initial value of ``Y`` (resp. ``X``):

.. literalinclude:: examples/swap_bad_depends.adb
   :language: ada
   :linenos:

|GNATprove| issues 3 check messages on ``Swap_Bad_Depends``:

.. literalinclude:: results/swap_bad_depends.flow
   :language: none

The last message informs us that the dependency ``Y => X`` stated in
``Swap_Bad_Depends``'s contract is incorrect for the given implementation. That
might be either an error in the code or an error in the contract. Here this is
an error in the code. The two other messages are consequences of this error.

Another possible contract is the postcondition introduced by aspect
``Post``. Here it specifies that the final value of ``X`` (resp. ``Y``) is
equal to the initial value of ``Y`` (resp. ``X``):

.. literalinclude:: examples/swap_bad_post.adb
   :language: ada
   :linenos:

|GNATprove| issues one check message on the unproved postcondition of
``Swap_Bad_Post``, with a counterexample giving concrete values of a wrong
execution:

.. literalinclude:: results/swap_bad_post.prove
   :language: none

Both the check messages on ``Swap_Bad_Depends`` and on ``Swap_Bad_Post`` inform
us that the intended functionality as expressed in the contracts is not
implemented in the procedure. And looking again at the warning issued by
|GNATprove| on ``Swap_Bad``, this was already pointing at the same issue:
swapping the values of ``X`` and ``Y`` should obviously lead to reading the
initial value of ``X``; the fact that this value is not used is a clear sign
that there is an error in the implementation. The correct version of ``Swap``
uses a temporary value to hold the value of ``X``:

.. literalinclude:: examples/swap.adb
   :language: ada
   :linenos:

|GNATprove| proves both contracts on ``Swap`` and it informs us that the
postcondition was proved:

.. literalinclude:: results/swap.prove
   :language: none

Let's now consider a well-known `in place` implementation of ``Swap`` that
avoids introducing a temporary variable by using bitwise operations:

.. literalinclude:: examples/swap_modulo.adb
   :language: ada
   :linenos:

|GNATprove| understands the bitwise operations on values of modular types, and
it proves here that the postcondition of ``Swap_Modulo`` is proved:

.. literalinclude:: results/swap_modulo.prove
   :language: none

|GNATprove|'s flow analysis issues warnings like the one on ``Swap_Bad``
whenever it detects that some variables or statements are not used in the
computation, which is likely uncovering an error. For example, consider
procedure ``Swap_Warn`` which assigns ``X`` and ``Tmp_Y`` out of order:

.. literalinclude:: examples/swap_warn.adb
   :language: ada
   :linenos:

On this wrong implementation, |GNATprove| issues a high check message for the
certain read of an uninitialized variable, and two warnings that point to
unused constructs:

.. literalinclude:: results/swap_warn.flow
   :language: none

In general, warnings issued by |GNATprove|'s flow analysis should be carefully
reviewed, as they may lead to the discovery of errors in the program.

.. _Addition:

Addition
^^^^^^^^

Consider a simple function ``Addition`` that returns the sum of its integer
parameters ``X`` and ``Y``. As in :ref:`Increment`, we add a suitable
precondition and postcondition for this function:

.. literalinclude:: examples/addition.adb
   :language: ada
   :linenos:

We also added flow dependencies to ``Addition`` for illustration purposes, but
they are the same as the default generated ones (the result of the function
depends on all its inputs), so are not in general given explicitly.

|GNATprove| issues a check message about a possible overflow in the
precondition of ``Addition``:

.. literalinclude:: results/addition.prove
   :language: none

Indeed, if we call for example ``Addition`` on values ``Integer'Last`` for
``X`` and ``1`` for ``Y``, the expression ``X + Y`` evaluated in the
precondition does not fit in a machine integer and raises an exception at run
time. In this specific case, some people may consider that it does not really
matter that an exception is raised due to overflow as the failure of the
precondition should also raise a run-time exception. But in general the
precondition should not fail (just consider the precondition ``X + Y not in
Integer`` for example), and even here, the different exceptions raised may be
treated differently (``Constraint_Error`` in the case of an overflow,
``Assertion_Error`` in the case of a failing precondition).

One way to avoid this vulnerability is to rewrite the precondition so that no
overflow can occur:

.. literalinclude:: examples/addition_rewrite.adb
   :language: ada
   :linenos:

Although |GNATprove| proves that ``Addition_Rewrite`` implements its contract
and is free from run-time errors, the rewritten precondition is not so readable
anymore:

.. literalinclude:: results/addition_rewrite.prove
   :language: none

A better way to achieve the same goal without losing in readability is to
execute and analyze contracts in a special mode where overflows cannot occur,
as explained in :ref:`Overflow Modes`. In that case, |GNATprove| proves that
there are no run-time errors in function ``Addition``, and that it implements
its contract.

Finally, we can choose to expand the range of applicability of the function, by
accepting any values of inputs ``X`` and ``Y``, and saturating when the
addition would overflow the bounds of machine integers. That's what function
``Addition_Saturated`` does, and its saturating behavior is expressed in
:ref:`Contract Cases`:

.. literalinclude:: examples/addition_saturated.adb
   :language: ada
   :linenos:

|GNATprove| proves that ``Addition_Saturated`` implements its contract and is
free from run-time errors:

.. literalinclude:: results/addition_saturated.prove
   :language: none

Note that we analyzed this function in ELIMINATED overflow mode, using the
switch ``-gnato13``, otherwise there would be possible overflows in the guard
expressions of the contract cases.


.. global/depends + errors
