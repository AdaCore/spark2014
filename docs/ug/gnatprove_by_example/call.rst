Call Examples
-------------

This section presents the results of running |GNATprove| on subprograms
calling other subprograms.

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
holds, i.e., ``X`` must be strictly less than ``Integer'Last``. One possible
approach here would be to guard each call to ``Increment`` with an ``if``
statement so that it is only called it the precondition is met. This would
make ``Add2`` saturate at ``Integer'Last``. However, the specification
of ``Add2`` has a postcondition stating that it must always increase
the value of ``X`` by two. The programmer discussed this postcondition with
the system designers and determined that it is fundamental to the correct
operation of the overall program so it cannot be changed. Therefore the right
thing to do here is add a suitable precondition to ``Add2``.

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
