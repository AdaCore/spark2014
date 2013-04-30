Basic Examples
--------------

This section presents the results of running CodePeer on simple subprograms
composed of assignments, branchings and calls.

Scalar Assignment
^^^^^^^^^^^^^^^^^

.. _assign:

.. rubric:: Assign

|GNATprove| is able to follow very precisely the assignments to scalar variables
throughout the program. Take a very simple program ``Assign`` that assigns the
value ``Y+1`` to the variable ``X``:

.. literalinclude:: /gnatprove_by_example/examples/t1q1.adb
   :language: ada
   :linenos:

On this subprogram, |GNATprove| generates the following flow errors:

.. literalinclude:: /gnatprove_by_example/results/t1q1.flow
   :language: none
   :linenos:

and the following proof results:

.. literalinclude:: /gnatprove_by_example/results/t1q1.prove
   :language: none
   :linenos:
