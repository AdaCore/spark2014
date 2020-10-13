Assertion Pragmas
=================

|SPARK| contains features for directing formal verification with
|GNATprove|. These features may also be used by other tools, in particular the
|GNAT Pro| compiler. Assertion pragmas are refinements of pragma ``Assert``
defined in Ada. For all assertion pragmas, an exception ``Assertion_Error`` is
raised at run time when the property asserted does not hold, if the program was
compiled with assertions. The real difference between assertion pragmas is how
they are used by |GNATprove| during proof.

.. index:: Assert

.. _Pragma Assert:

Pragma ``Assert``
-----------------

[Ada 2005]

Pragma ``Assert`` is the simplest assertion pragma. |GNATprove| checks that the
property asserted holds, and uses the information that it holds for analyzing
code that follows. For example, consider two assertions of the same property
``X > 0`` in procedure ``Assert_Twice``:

.. literalinclude:: /examples/tests/assert_twice/assert_twice.adb
   :language: ada
   :linenos:

As expected, the first assertion on line 5 is not provable in absence of a
suitable precondition for ``Assert_Twice``, but |GNATprove| proves that it
holds the second time the property is asserted on line 6:

.. literalinclude:: /examples/tests/assert_twice/test.out
   :language: none

|GNATprove| considers that an execution of ``Assert_Twice`` with ``X <= 0``
stops at the first assertion that fails. Thus ``X > 0`` when execution reaches
the second assertion.  This is true if assertions are executed at run time, but
not if assertions are discarded during compilation. In the latter case,
unproved assertions should be inspected carefully to ensure that the property
asserted will indeed hold at run time. This is true of all assertion pragmas,
which |GNATprove| analyzes like pragma ``Assert`` in that respect.

.. index:: Assertion_Policy

.. _Pragma Assertion_Policy:

Pragma ``Assertion_Policy``
---------------------------

[Ada 2005/Ada 2012]

Assertions can be enabled either globally or locally. Here, *assertions* denote
either :ref:`Assertion Pragmas` of all kinds (among which :ref:`Pragma Assert`)
or functional contracts of all kinds (among which :ref:`Preconditions` and
:ref:`Postconditions`).

By default, assertions are ignored in compilation, and can be enabled globally
by using the compilation switch ``-gnata``. They can be enabled locally by
using pragma ``Assertion_Policy`` in the program, or globally if the pragma is
put in a configuration file. They can be enabled for all kinds of assertions or
specific ones only by using the version of pragma ``Assertion_Policy`` that
takes named associations which was introduced in Ada 2012.

When used with the standard policies ``Check`` (for enabling assertions) or
``Ignore`` (for ignoring assertions), pragma ``Assertion_Policy`` has no
effect on |GNATprove|. |GNATprove| takes all assertions into account, whatever
the assertion policy in effect at the point of the assertion. For example,
consider a code with some assertions enabled and some ignored:

.. literalinclude:: /examples/tests/assert_enabled/assert_enabled.adb
   :language: ada
   :linenos:

Although the postcondition and the second assertion are not executed at run
time, |GNATprove| analyzes them and issues corresponding messages:

.. literalinclude:: /examples/tests/assert_enabled/test.out
   :language: none

On the contrary, when used with the GNAT-specific policy ``Disable``, pragma
``Assertion_Policy`` causes the corresponding assertions to be skipped both
during execution and analysis with |GNATprove|. For example, consider the same
code as above where policy ``Ignore`` is replaced with policy ``Disable``:

.. literalinclude:: /examples/tests/assert_disabled/assert_disabled.adb
   :language: ada
   :linenos:

On this program, |GNATprove| does not analyze the postcondition and the second
assertion, and it does not issue corresponding messages:

.. literalinclude:: /examples/tests/assert_disabled/test.out
   :language: none

The policy of ``Disable`` should thus be reserved for assertions that are not
compilable, typically because a given build environment does not define the
necessary entities.

.. index:: Loop_Invariant

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

.. literalinclude:: /examples/tests/simple_loops/simple_loops.adb
   :language: ada
   :lines: 6-10
   :lineno-match:

Thus, |GNATprove| checks that property 2 holds but not property 1:

.. literalinclude:: /examples/tests/simple_loops/test.out
   :language: none
   :lines: 3-7

Conversely, in the following loop, the loop invariant is true during the first
iteration and false in all remaining iterations:

.. literalinclude:: /examples/tests/simple_loops/simple_loops.adb
   :language: ada
   :lines: 12-16
   :lineno-match:

Thus, |GNATprove| checks that property 1 holds but not property 2:

.. literalinclude:: /examples/tests/simple_loops/test.out
   :language: none
   :lines: 8-13

The following loop shows a case where the loop invariant holds both during the
first iteration and all remaining iterations:

.. literalinclude:: /examples/tests/simple_loops/simple_loops.adb
   :language: ada
   :lines: 18-22
   :lineno-match:

|GNATprove| checks here that both properties 1 and 2 hold:

.. literalinclude:: /examples/tests/simple_loops/test.out
   :language: none
   :lines: 14,15

In general, it is not sufficient that a loop invariant is true for |GNATprove|
to prove it. The loop invariant should also be `inductive`: it should be
precise enough that |GNATprove| can check loop invariant preservation by
assuming `only` that the loop invariant held during the last iteration. For
example, the following loop is the same as the previous one, except the loop
invariant is true but not inductive:

.. literalinclude:: /examples/tests/simple_loops/simple_loops.adb
   :language: ada
   :lines: 24-28
   :lineno-match:

|GNATprove| cannot check property 2 on that loop:

.. literalinclude:: /examples/tests/simple_loops/test.out
   :language: none
   :lines: 16-21

Note that using |CodePeer| static analysis allows here to fully prove the
loop invariant, which is possible because |CodePeer| generates its own sound
approximation of loop invariants (see :ref:`Using CodePeer Static Analysis` for
details):

.. literalinclude:: /examples/tests/simple_loops_cdp/test.out
   :language: none
   :lines: 15

Note also that not using an assertion (:ref:`Pragma Assert`) instead of a loop
invariant also allows here to fully prove the corresponding property, by
relying on :ref:`Automatic Unrolling of Simple For-Loops`:

.. literalinclude:: /examples/tests/simple_loops_unroll/test.out
   :language: none
   :lines: 3

Returning to the case where neither automatic loop unrolling nor |CodePeer| are
used, the reasoning of |GNATprove| for checking property 2 in that case can be
summarized as follows:

* Let's take iteration K of the loop, where K > 1 (not the first iteration).
* Let's assume that the loop invariant held during iteration K-1, so we know
  that if K-1 > 1 then Prop holds.
* The previous assumption can be rewritten: if K > 2 then Prop.
* But all we know is that K > 1, so we cannot deduce Prop.

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

Finally, :ref:`Attribute Loop_Entry` and :ref:`Delta Aggregates` can be very
useful to express complex loop invariants.

.. note::

   Users that are already familiar with the notion of loop invariant in other
   proof systems should be aware that loop invariants in |SPARK| are slightly
   different from the usual ones. In |SPARK|, a loop invariant must hold when
   execution reaches the corresponding pragma inside the loop. Hence, it needs
   not hold when the loop is never entered, or when exiting the loop.

.. index:: Loop_Variant
           termination; loop variant

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

.. literalinclude:: /examples/tests/terminating_loops/terminating_loops.adb
   :language: ada
   :linenos:

|GNATprove| is able to prove both loop variants, as well as absence of run-time
errors in the subprogram, hence that loops terminate:

.. literalinclude:: /examples/tests/terminating_loops/test.out
   :language: none

Pragma ``Loop_Variant`` may appear anywhere a loop invariant appears. It is
also possible to use multiple loop variants, which should be grouped together
with loop invariants. A loop variant may be more complex than a single
decreasing (or increasing) value, and be given instead by a list of either
decreasing or increasing values (possibly a mix of both). In that case, the
order of the list defines the lexicographic order of progress. See |SPARK| RM
5.5.3 for details.

.. index:: Assume

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

.. literalinclude:: /examples/tests/assume_then_assert/assume_then_assert.adb
   :language: ada
   :linenos:

As expected, |GNATprove| does not check the property on line 5, but used it to
prove that the assertion holds on line 6:

.. literalinclude:: /examples/tests/assume_then_assert/test.out
   :language: none

|GNATprove| considers that an execution of ``Assume_Then_Assert`` with ``X <=
0`` stops at the assumption on line 5, and it does not issue a message in that
case because the user explicitly indicated that this case is not possible. Thus
``X > 0`` when execution reaches the assertion on line 6. This is true if
assertions (of which assumptions are a special kind) are executed at run time,
but not if assertions are discarded during compilation. In the latter case,
assumptions should be inspected carefully to ensure that the property assumed
will indeed hold at run time. This inspection may be facilitated by passing a
justification string as the second argument to pragma ``Assume``.

.. index:: Assert_And_Cut

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

.. literalinclude:: /examples/tests/forgetful_assert/forgetful_assert.adb
   :language: ada
   :linenos:

|GNATprove| proves that the assertion on line 7 holds, but it cannot prove that
the same assertion on line 12 holds:

.. literalinclude:: /examples/tests/forgetful_assert/test.out
   :language: none

|GNATprove| *forgets* the exact value of ``X`` after line 9. All it knows is
the information given in pragma ``Assert_And_Cut``, here that ``X > 0``. And
indeed |GNATprove| proves that such an assertion holds on line 11. But it
cannot prove the assertion on line 12, and the counterexample displayed
mentions a possible value of 2 for ``X``, showing indeed that |GNATprove|
forgot its value of 1.

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
