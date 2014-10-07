Basic Proof Examples
--------------------

The remaining examples in this section show the use of |GNATprove| for formal
verification. We start by looking at the results of running |GNATprove| on
simple subprograms composed of assignments and branches.  Note that the
remaining examples generally do not
have ``Global`` and ``Depends`` annotations present as we want to focus on
formal verification. In practise the contracts for flow analysis and proof
can, of course, co-exist happily together.

Scalar Assignment
^^^^^^^^^^^^^^^^^

.. _assign:

.. rubric: : Assign (no need for using rubric now as there is only one example)

|GNATprove| is able to follow very precisely the assignments to scalar variables
throughout the program. Take a very simple program ``Increment`` that assigns the
value ``X+1`` to the variable ``X``. This subprogram does not have any annotations
to specify what its behaviour should be so |GNATprove| has no specification to
verify it against. It will, however, attempt to prove that none of Ada's predefined
exceptions can be raised during its execution.

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

.. rubric: : Swap (no need for using rubric now as there is only one example)

In the previous example |GNATprove| was able to prove that the subprogram
was free from run-time exceptions but it did not help us with the question
of whether the subprogram performed its intended function. Why not? Because
we did not provide any specification of what the subprogram is supposed to
do. We can specify properties about the required results of subprograms by
adding postconditions to them, then using |GNATprove| to check that those
postconditions hold.

To illustrate the use of postconditions, consider the subprogram ``Swap``
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

.. rubric: : Nand (no need for using rubric now as there is only one example)

Now we turn to a procedure ``NandGate`` which calculates the NAND
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

.. rubric: : NextDay (no need for using rubric now as there is only one example)

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
of the ``'Succ`` attribute could potentially cause a run-time error if ``Today`` is
the last value in the type. However, the ``if`` statement guards against this so
the check is proved.

.. literalinclude:: gnatprove_by_example/results/t1q3c.prove
   :language: none
   :linenos:

Bounded_Addition
^^^^^^^^^^^^^^^^

.. _boundedadd:

.. rubric: : BoundedAdd (no need for using rubric now as there is only one example)

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
no run-time errors. You may be wondering how it is that the postcondition
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
