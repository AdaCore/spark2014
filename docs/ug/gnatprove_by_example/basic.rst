Basic Examples
--------------

This section presents the results of running |GNATprove| on simple subprograms
composed of assignments, branches and calls.

Scalar Assignment
^^^^^^^^^^^^^^^^^

.. _assign:

.. rubric:: Assign

|GNATprove| is able to follow very precisely the assignments to scalar variables
throughout the program. Take a very simple program ``Increment`` that assigns the
value ``X+1`` to the variable ``X``:

.. literalinclude:: gnatprove_by_example/examples/t1q1a.adb
   :language: ada
   :linenos:

The proof results show that |GNATprove| is unable to prove the overflow
check on line 7, where ``X`` is incremented. This is not surprising, given
that the initial value of ``X`` could be ``Integer'Last`` and incrementing
it would indeed cause an overflow in this case.

.. literalinclude:: gnatprove_by_example/results/t1q1a.prove
   :language: none
   :linenos:

We can guard against this possibility by adding a suitable precondition
to the specification of ``Increment``. This states that that ``X``
must always be strictly less than ``Integer'Last`` at the point where
the subprogram is called.

.. literalinclude:: gnatprove_by_example/examples/t1q1b.ads
   :language: ada
   :linenos:

|GNATprove| assumes that the precondition holds when it performs the proof
of ``Increment``. For any subprogram which calls ``Increment``, |GNATprove|
will check that the precondition holds at the point of the call. 

.. literalinclude:: gnatprove_by_example/results/t1q1b.prove
   :language: none
   :linenos:

Swap
^^^^

.. _swap:

.. rubric:: Swap

In the previous example |GNATprove| was able to prove that the subprogram
was free from runtime exceptions but it did not help us with the question
of whether the subprogram performed its intended function. Why not? Because
we did not provide any specification of what the subprogram is supposed to
do. We can specify properties about the required results of subprograms by
adding postconditions to them, then using |GNATprove| to check that those
postconditions hold.

To illustrate the use of postconditions, condsider the subprogram ``Swap``
which exchanges the values of its two parameters ``X`` and ``Y``. The ``Post``
aspect states that the new value of ``X`` will be the initial value of ``Y``
and vice-versa. Note the use of the ``'Old`` attribute to refer to the initial
values of the parameters.

.. literalinclude:: gnatprove_by_example/examples/t1q3a.ads
   :language: ada
   :linenos:

The body of ``Swap`` makes use of a temporary variable to exchange the
values of ``X`` and ``Y`` in the standard way.

.. literalinclude:: gnatprove_by_example/examples/t1q3a.adb
   :language: ada
   :linenos:

The proof results show that |GNATprove| is able to prove that the postcondition
holds.

.. literalinclude:: gnatprove_by_example/results/t1q3a.prove
   :language: none
   :linenos:

NAND 
^^^^

.. _nand:

.. rubric:: Nand

Now we turn to a procedure ``Nandgate`` which calculates the NAND
of two Boolean values. Here the programmer has decided to specify
the postcondition by enumerating all the entries in the truth
table for a NAND function. This could have been written using the
``Post`` aspect like this:

.. code-block:: ada

   with Post => ((if ((not P) and (not Q)) then R) and
                 (if ((not P) and Q) then R) and
                 (if (P and (not Q)) then R) and
                 (if (P and Q) then (not R)));

However, the ``Contract_Cases`` aspect provides a convenient way
to write this type of postcondition, as shown below:

.. literalinclude:: gnatprove_by_example/examples/t1q3b.ads
   :language: ada
   :linenos:

The implementation is much simpler than the specification. This
simplified expression for NAND could have been used in the specification
as they are equivalent, but our programmer wanted to use the
more efficient form in the implementation whilst keeping the more 
explicit version in the specification.

.. literalinclude:: gnatprove_by_example/examples/t1q3b.adb
   :language: ada
   :linenos:

The proof results show that |GNATprove| is able to prove that the postcondition
holds, thus demonstrating that the simple expression in the body does indeed
implement a NAND function. Note how the results show that each individual contract
case was proved and that the overall contract was proved.

.. literalinclude:: gnatprove_by_example/results/t1q3b.prove
   :language: none
   :linenos:

NextDay
^^^^^^^

.. _nextday:

.. rubric:: NextDay

The next example shows two subprograms, ``NextDay_A`` and ``NextDay_B``, both
of which have the same postcondition. Given a value of the enumeration type 
``Day`` they will give the value of the next day. Naturally, this wraps around
so if the day is Sunday (the last value in the enumeration) then the next day
is Monday (the first value).

.. literalinclude:: gnatprove_by_example/examples/t1q3c.ads
   :language: ada
   :linenos:

The bodies of the two subprograms illustrate two alternative implementations
of the next day functionality. The first one uses the ``'Succ`` attribute to
get the next day, with a special case for Sunday as it is the last value in
the type. The second version uses a case statement to state explicitly what
the output should be for each input. 

.. literalinclude:: gnatprove_by_example/examples/t1q3c.adb
   :language: ada
   :linenos:

The proof results show that |GNATprove| is able to prove that both implementations
meet their postconditions. There is also a range check on line 11, because the use
of the ``'Succ`` attribute could potentially cause a runtime error if ``Today`` is
the last value in the type. However, the ``if`` statement guards against this so
the check is proved.

.. literalinclude:: gnatprove_by_example/results/t1q3c.prove
   :language: none
   :linenos:

Bounded_Addition
^^^^^^^^^^^^^^^^

.. _boundedadd:

.. rubric:: BoundedAdd

The procedure ``Bounded_Add`` takes two Integer values and calculates their
sum. If the result would exceed the bounds of the Integer type then it should
saturate at the maximum or minimum Integer value. The ``Contract_Cases`` aspect
gives a natural way to express this specification.

.. literalinclude:: gnatprove_by_example/examples/t1q5.ads
   :language: ada
   :linenos:

The tricky part is to implement this in the body without making use of a
type that is larger than Integer. (If the implementation simply added the
two values together to see if the result exceeded the bounds of Integer
then it would obviously need a larger type to store the result.)

.. literalinclude:: gnatprove_by_example/examples/t1q5.adb
   :language: ada
   :linenos:

The proof results show that |GNATprove| is able to prove all the checks
for this subprogram, so it satisifes its postcondition and there are 
no runtime errors. You may be wondering how it is that the postcondition
in the subprogram specification contains an expression which simply
adds together the two Integers, yet this does not overflow. This is
because the project file specifies the compiler switch ``-gnato13``
to define the semantics when calculating intermediate expressions.
The first digit specifies the semantics for general code, with ``1``
meaning that the normal Ada type system semantics should be used. The
second digit specifies the semantics for use in proof (preconditions,
postconditions, assertions, invariants), with ``3`` meaning that mathematical
semantics are used so there is no possibility of overflow. If this
option were changed to ``-gnato11`` then the normal Ada type system
semantics would be used in proof expressions and |GNATprove| would
(quite rightly) not be able to prove that there was no possibility
of overflow in the postcondition. This is an important option and we
recommend that users read the documentation carefully in order to 
understand how it behaves.

.. literalinclude:: gnatprove_by_example/results/t1q5.prove
   :language: none
   :linenos:

Call Examples
-------------

Increment Revisited
^^^^^^^^^^^^^^^^^^^

Earlier on we saw a procedure ``Increment`` which takes an Integer ``X``
and increments it by 1. In order to prove that the statement which adds
1 to ``X`` cannot result in an overflow we specified the precondition
that ``X < Integer'Last``. To see how this precondition is used, let's
consider a procedure ``Add2`` which adds two to an Integer by making 
multiple calls to ``Increment``.

.. literalinclude:: gnatprove_by_example/examples/t1q1c.adb
   :language: ada
   :linenos:

If we try to prove this with |GNATprove| it reports the following:

.. literalinclude:: gnatprove_by_example/results/t1q1c.prove
   :language: none
   :linenos:

For each call to ``Increment`` we are required to show that its precondition
holds, i.e. ``X`` must be strictly less than ``Integer'Last``. One possible
approach here would be to guard each call to ``Increment`` with an ``if``
statement so that it is only called it the precondition is met. This would
make ``Increment2`` saturate at ``Integer'Last``. However, the specification
of ``Increment2`` has a postcondition stating that it must always increase
the value of ``X`` by two. The programmer discussed this postcondition with
the system designers and determined that it is fundamental to the correct
operation of the overall program so it cannot be changed. Therefore the right
thing to do here is add a suitable precondition to ``Increment2``.

.. literalinclude:: gnatprove_by_example/examples/t1q1d.ads
   :language: ada
   :linenos:

Having added this precondition, |GNATprove| is able to prove that the 
precondition on the first call to ``Increment`` always holds, but it
fails to prove it for the second call, and it fails to prove the
postcondition on ``Add2``. What's going on?

.. literalinclude:: gnatprove_by_example/results/t1q1d.prove
   :language: none
   :linenos:

The trouble is that there is no postcondition specified for ``Increment`` so
|GNATprove| knows nothing about the value of ``X`` after each call to ``Increment``
(other than that it is in the range of Integer). So let's add a postcondition
to ``Increment`` saying what it does.

.. literalinclude:: gnatprove_by_example/examples/t1q1e.ads
   :language: ada
   :linenos:

Now |GNATprove| is able to prove all the checks and contracts.

.. literalinclude:: gnatprove_by_example/results/t1q1e.prove
   :language: none
   :linenos:

Loop Examples
-------------

Integer Square Root
^^^^^^^^^^^^^^^^^^^

.. _intsqrt:

.. rubric:: IntSqrt

The procedure ``ISQRT`` calculates the integer square root of a natural number.
The postcondition specifies that the required result ``Root`` must have a value
such that ``Root`` squared is less than or equal to the input value but ``Root + 1``
squared must be strictly greater than the input value.

.. literalinclude:: gnatprove_by_example/examples/t1q4.ads
   :language: ada
   :linenos:

The implementation in the body is not particularly efficient! It simply starts
at 0 and increments the potential answer by 1 each time around the loop until
it finds a value that satisfies the specification. In order to prove properties
about code involving loops it is normally necessary to provide a loop invariant.
In |GNATprove| this is done by means of the pragma ``Loop_Invariant`` which, in
this case, states that the current candidate answer ``Local_Root`` squared is
less than or equal to the input value ``N`` and is less than or equal to 
``Natural'Last``. Note the use of the larger type ``Big_Natural`` which has been
introduced because the result of squaring a Natural could clearly exceed the range of
the type Natural. Observe that the invariant has been placed just before the end
of the loop as this is the natural place for it in this particular example - there
is no need for invariants to be placed right at the top of loops.

.. literalinclude:: gnatprove_by_example/examples/t1q4.adb
   :language: ada
   :linenos:

The proof results show that |GNATprove| is able to prove all the checks for the
loop invariant (which must be shown to hold for the path leading into the loop,
and for the path back around the loop), the postcondition, and for overflow and
range checks.

.. literalinclude:: gnatprove_by_example/results/t1q4.prove
   :language: none
   :linenos:


Advanced Examples
-----------------

Assert and Cut
^^^^^^^^^^^^^^

.. _assert_and_cut:

.. rubric:: Assert_And_Cut

In this example the procedure ``Increment2`` which takes two parameters ``X``
and ``Y``. The postcondition on the specification states that both parameters
will be incremented. The precondition guards against overflow, and must be
shown to hold for any subprogram which calls ``Increment2``.

.. literalinclude:: gnatprove_by_example/examples/t1q2.ads
   :language: ada
   :linenos:

Here is the body. Note the use of the pragma
``Assert_And_Cut`` which splits the subprogram into two paths for proof
purposes. |GNATprove| must show that the assertion is true for the path
from the beginning of the subprogram to the pragma. The assertion is then
known to be true for the path from the pragma to the end of the subprogram
(for which the postcondition must be shown to hold).

.. literalinclude:: gnatprove_by_example/examples/t1q2.adb
   :language: ada
   :linenos:

The proof results show that all checks are proved:

.. literalinclude:: gnatprove_by_example/results/t1q2.prove
   :language: none
   :linenos:

