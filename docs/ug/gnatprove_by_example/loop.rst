Loop Examples
-------------

This section presents the results of running |GNATprove| on subprograms
containing loops.

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
range checks. (Note that to ensure that the loop invariant is free from overflow
the compiler switch ``-gnato13`` was specified, as explained earlier for the bounded
addition example.)

.. literalinclude:: gnatprove_by_example/results/t1q4.prove
   :language: none
   :linenos:

SumArray
^^^^^^^^

Here is a more complex loop example, this time using a ``for`` loop. The function
``SumArray`` calculates the sum of the values of the elements of an array. The
array has 100 elements, each of which may be in the range 0 to 1000. A suitable
subtype has been defined to store the result. 

.. literalinclude:: gnatprove_by_example/examples/t3q4.ads
   :language: ada
   :linenos:

The loop invariant states that the current value of the sum is equal to the sum
of the elements that have been iterated over so far, and cannot be more than
1000 times the number of elements iterated over so far. The expression function
``Summed_Between`` has been defined to help with this and is needed for proof
purposes only as it only appears in the loop invariant.

.. literalinclude:: gnatprove_by_example/examples/t3q4.adb
   :language: ada
   :linenos:

The proof results show that |GNATprove| is able to prove all checks for this
example.

.. literalinclude:: gnatprove_by_example/results/t3q4.prove
   :language: none
   :linenos:

