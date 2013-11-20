Flow Analysis Examples
----------------------

This section presents the results of running |GNATprove| in flow
analysis mode on a number of examples to illustrate the various flow
errors and warnings that might be raised. Note the use of
``pragma SPARK_Mode`` to identify each example as SPARK.

Here is the specification of a swap subprogram along with flow
analysis contracts. The ``Global`` aspect is ``null``, specifying
that this subprogram does not reference any global variables and,
therefore, has no side-effects. The ``Depends`` aspect states that
the final value of ``X`` depends only on the initial value of ``Y``,
and the final value of ``Y`` depends only on the initial value of ``X``.
Neither ``X`` nor ``Y`` depends on its own initial value.

.. literalinclude:: gnatprove_by_example/examples/swap_incorrect_a.ads
   :language: ada
   :linenos:

Below is a flawed implementation in which the value of ``Y`` is assigned
to ``X`` but then the same value is assigned back to ``Y``.

.. literalinclude:: gnatprove_by_example/examples/swap_incorrect_a.adb
   :language: ada
   :linenos:

|GNATprove| detects that this body does not satisfy the subprogram's
dependency contract and reports the following flow errors.

.. literalinclude:: gnatprove_by_example/results/swap_incorrect_a.flow
   :language: none
   :linenos:

In the next attempt, the values of ``X`` and ``Y`` are correctly swapped
but the subprogram also increments a call counter.

.. literalinclude:: gnatprove_by_example/examples/swap_incorrect_b.adb
   :language: ada
   :linenos:

The call counter is a global variable that is both read and written by
the subprogram, but the global aspect specified that the subprogram did
not reference any global variables, so |GNATprove| reports the following
error.

.. literalinclude:: gnatprove_by_example/results/swap_incorrect_b.flow
   :language: none
   :linenos:

This implementation contains an ineffective statement (the
initialization of ``Old_X`` at declaration) and an unused variable.

.. literalinclude:: gnatprove_by_example/examples/swap_incorrect_c.adb
   :language: ada
   :linenos:

Both errors are detected and reported by |GNATprove| when it analyses the
body.

.. literalinclude:: gnatprove_by_example/results/swap_incorrect_c.flow
   :language: none
   :linenos:

Finally, this implementation of ``Swap`` contains the use of an
uninitialized variable.

.. literalinclude:: gnatprove_by_example/examples/swap_incorrect_d.adb
   :language: ada
   :linenos:

This results in the following flow errors being reported by |GNATprove|.

.. literalinclude:: gnatprove_by_example/results/swap_incorrect_d.flow
   :language: none
   :linenos:
