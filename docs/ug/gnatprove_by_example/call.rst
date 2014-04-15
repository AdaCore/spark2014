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
holds, i.e. ``X`` must be strictly less than ``Integer'Last``. One possible
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

Local Subprograms
^^^^^^^^^^^^^^^^^

It may be convenient to create local subprograms without necessarily specifying
a contract for these. |GNATprove| attempts to perform a contextual analysis of
these local subprograms without contract, at each call site, as if the code of
the subprograms was inlined. Thus, the analysis proceeds in that case as if it
had the most precise contract for the local subprogram, in the context of its
calls.

Let's consider as previously a subprogram which adds two to its integer input:

.. literalinclude:: gnatprove_by_example/examples/arith_with_local_subp.ads
   :language: ada
   :linenos:

And let's implement it by calling two local subprograms without contracts
(which may or not have a separate declaration), which each increment the input
by one:

.. literalinclude:: gnatprove_by_example/examples/arith_with_local_subp.adb
   :language: ada
   :linenos:

|GNATprove| would not be able to prove that the addition in
``Increment_In_Body`` or ``Increment_Nested`` cannot overflow in any
context. If it was using only the default contract for these subprograms, it
also would not prove that the contract of ``Add_Two`` is respected.  But since
it analyzes these subprograms in the context of their calls only, it proves
here that no overflow is possible, and that the two increments correctly
implement the contract of ``Add_Two``:

.. literalinclude:: gnatprove_by_example/results/arith_with_local_subp.prove
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
and then proceeds to analyze it normally, using the default contract.

Note that it is very simple to prevent contextual analysis of a local
subprogram, by adding a contract to it, for example a simple ``Pre => True`` or
``Global => null``.

Otherwise, both flow analysis and proof are done for the subprogram in the
context of its calls.
