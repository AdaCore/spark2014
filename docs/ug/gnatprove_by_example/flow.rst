Flow Analysis Examples
----------------------

This section presents the results of running |GNATprove| on a number
of examples to illustrate the various flow error and warnings that
might be raised.

Below is the specification of a swap subprogram along with flow
analysis contracts. The ``Global`` aspects states that this subprogram
definitely has no side-effects as forbids the use of any global
variables. The ``Depends`` aspect states that information should flow
from X to Y and vice versa, but in particular X (and Y) should not in
any way depend on itself.

.. literalinclude:: gnatprove_by_example/examples/swap_incorrect_a.ads
   :language: ada
   :linenos:

Below is a flawed implementation.

.. literalinclude:: gnatprove_by_example/examples/swap_incorrect_a.ads
   :language: ada
   :linenos:

And the flow errors which will be raised on this body.

.. literalinclude:: gnatprove_by_example/results/swap_incorrect_a.flow
   :language: none
   :linenos:

In this flawed implementation we increment a call counter.

.. literalinclude:: gnatprove_by_example/examples/swap_incorrect_b.adb
   :language: ada
   :linenos:

And the flow errors which will be raised on this body.

.. literalinclude:: gnatprove_by_example/results/swap_incorrect_b.flow
   :language: none
   :linenos:

This implementation contains an ineffective statement (the
initialisation of Old_X at declaration) and an unused variable.

.. literalinclude:: gnatprove_by_example/examples/swap_incorrect_c.adb
   :language: ada
   :linenos:

And the flow errors which will be raised on this body.

.. literalinclude:: gnatprove_by_example/results/swap_incorrect_c.flow
   :language: none
   :linenos:

Finally, this implementation of swap contains the use of an
uninitialized variable:

.. literalinclude:: gnatprove_by_example/examples/swap_incorrect_d.adb
   :language: ada
   :linenos:

And the flow errors which will be raised on this body.

.. literalinclude:: gnatprove_by_example/results/swap_incorrect_d.flow
   :language: none
   :linenos:
