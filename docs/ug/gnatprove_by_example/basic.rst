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

.. literalinclude:: gnatprove_by_example/examples/t1q1.adb
   :language: ada
   :linenos:

.. RPM: I think we should delete all the flow analysis sections which
.. don't show anything interesting, such as this one.

On this subprogram, |GNATprove| generates the following flow errors:

.. literalinclude:: gnatprove_by_example/results/t1q1.flow
   :language: none
   :linenos:

and the following proof results:

.. literalinclude:: gnatprove_by_example/results/t1q1.prove
   :language: none
   :linenos:

You may be wondering how |GNATprove| managed to prove that ``X + 1`` does
not overflow, given that ``X`` is an Integer. The answer lies in the 
specification of ``Increment`` which states the precondition that ``X``
must be strictly less than ``Integer'Last``.

.. literalinclude:: gnatprove_by_example/examples/t1q1.ads
   :language: ada
   :linenos:

|GNATprove| assumes that the precondition holds when it performs the proof
of ``Increment``. For any subprogram which calls ``Increment``, |GNATprove|
will check that the precondition holds at the point of the call. Note also
the postcondition which states that ``Increment`` does indeed add one to ``X``.
As you would expect, |GNATprove| is able to prove this easily as shown by
the proof results.

Assert and Cut
^^^^^^^^^^^^^^

.. _assert_and_cut:

.. rubric:: Assert_And_Cut

Here we have a similar example ``Increment2`` which takes two parameters ``X``
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

On this subprogram, |GNATprove| generates the following flow errors:

.. literalinclude:: gnatprove_by_example/results/t1q2.flow
   :language: none
   :linenos:

The flow errors relate to the constants ``X_Old`` and ``Y_Old`` which have
been introduced to capture the initial values of ``X`` and ``Y`` so that they
can be referred to in the pragma. (The attribute ``'Old`` may only be used
in postconditions.) In future, a more elegant solution will be to use ghost
variables but these have not yet been implemented in |GNATprove|.
*Flow errors are not appearing at present*

The proof results show that all checks are proved:

.. literalinclude:: gnatprove_by_example/results/t1q2.prove
   :language: none
   :linenos:

Swap
^^^^

.. _swap:

.. rubric:: Swap

As another illustration of postconditions, condsider the subprogram ``Swap``
which exchanges the values of its two parameters. Note the use of the
``'Old`` attribute to refer to the initial values of the parameters.

.. literalinclude:: gnatprove_by_example/examples/t1q3a.ads
   :language: ada
   :linenos:

The body of ``Swap`` makes use of a temporary variable to exchange the
values of ``X`` and ``Y`` in the standard way.

.. literalinclude:: gnatprove_by_example/examples/t1q3a.adb
   :language: ada
   :linenos:

On this subprogram, |GNATprove| generates the following flow errors:

.. literalinclude:: gnatprove_by_example/results/t1q3a.flow
   :language: none
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
of two Boolean values. The postcondition on the specification 
enumerates all four possible input conditions and specifies the
required output for each one.

.. literalinclude:: gnatprove_by_example/examples/t1q3b.ads
   :language: ada
   :linenos:

The implementation is much simpler than the specification. This
simplified expression for NAND could have been used in the specification
as they are equivalent, but perhaps the programmer wanted to use the
more efficient form in the implementation whilst keeping the more 
explicit version in the specification.

.. literalinclude:: gnatprove_by_example/examples/t1q3b.adb
   :language: ada
   :linenos:

On this subprogram, |GNATprove| generates the following flow errors:

.. literalinclude:: gnatprove_by_example/results/t1q3b.flow
   :language: none
   :linenos:

The proof results show that |GNATprove| is able to prove that the postcondition
holds, thus demonstrating that the simple expression in the body does indeed
implement a NAND function.

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
the output should be for each input. This is almost identical to the specification
so it might be easier to prove.

.. literalinclude:: gnatprove_by_example/examples/t1q3c.adb
   :language: ada
   :linenos:

On this subprogram, |GNATprove| generates the following flow errors:

.. literalinclude:: gnatprove_by_example/results/t1q3c.flow
   :language: none
   :linenos:

The proof results show that |GNATprove| is able to prove that both implementations
meet their postconditions. There is also a range check on line 11, because the use
of the ``'Succ`` attribute could potentially cause a runtime error if ``Today`` is
the last value in the type. However, the ``if`` statement guards against this so
the check is proved.

.. literalinclude:: gnatprove_by_example/results/t1q3c.prove
   :language: none
   :linenos:

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

On this subprogram, |GNATprove| generates the following flow errors:

.. literalinclude:: gnatprove_by_example/results/t1q4.flow
   :language: none
   :linenos:

The proof results show that |GNATprove| is able to prove all the checks for the
loop invariant (which must be shown to hold for the path leading into the loop,
and for the path back around the loop), the postcondition, and for overflow and
range checks.

.. literalinclude:: gnatprove_by_example/results/t1q4.prove
   :language: none
   :linenos:

