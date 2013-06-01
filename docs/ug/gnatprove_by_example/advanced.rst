Advanced Examples
-----------------

This section presents the results of running |GNATprove| with some advanced
features.

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

