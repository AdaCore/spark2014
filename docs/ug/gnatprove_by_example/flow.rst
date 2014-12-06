Flow Analysis Examples
----------------------

This section presents the results of running |GNATprove| in flow
analysis mode on a number of examples to illustrate the various flow
errors and warnings that might be raised. Note the use of
``pragma SPARK_Mode`` to identify each example as SPARK.

Analysis of non-returning subprograms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A special case are subprograms which implement the main control loop:
infinite loops in subprograms with outputs (globals or parameters of mode
out or in out) are treated differently. Consider the following example:

.. literalinclude:: gnatprove_by_example/examples/main3.adb
   :language: ada
   :linenos:

Here, we have implemented the main control loop in the subprogram Control,
but although the subprogram is marked to not return flow analysis does take
the overall effects into account which results in "as expected" dependency
relations.

Analysis of volatile objects
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In SPARK, library level variables can be marked volatile, and their exact
behaviour can be described in more detail than is possible in Ada. First, a
basic example featuring a scalar and composite volatile object:

.. literalinclude:: gnatprove_by_example/examples/volatile_example_a.adb
   :language: ada
   :linenos:

Note that currently only entire-object access to volatiles is supported:
this means the composite volatile in the above example must be read and
assign as a whole variable. Further note that volatiles are assumed to
change at any point, so the assertion in the above example is not provable.
