Flow Analysis Examples
----------------------

This section presents the results of running |GNATprove| in flow
analysis mode on a number of examples to illustrate the various flow
errors and warnings that might be raised. Note the use of
``pragma SPARK_Mode`` to identify each example as SPARK.

Analysis of non-returning subprograms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

It is possible to mark subprograms in SPARK 2014 as non-returning, using
the Ada 2014 No_Return aspect. In SPARK 2014 contracts are always specified
with respect to the condition that the subprogram terminates, and the flow
contracts are no exception.

Consider the following example:

.. literalinclude:: gnatprove_by_example/examples/no_return_a.adb
   :language: ada
   :linenos:

Flow analysis does, by default, not know that Halt does not actually
return, so the following error messages are produced (it helps to imagine
that the call to Halt is a null statement):

.. literalinclude:: gnatprove_by_example/results/no_return_a.flow
   :language: none
   :linenos:

To resolve this, it is possible to mark a subprogram as non-returning, as
shown in the revised example below:

.. literalinclude:: gnatprove_by_example/examples/no_return_b.adb
   :language: ada
   :linenos:

The analysis of the corrected program yields no errors or warnings, and
flow analysis also checks that any subprogram marked with No_Return either
always throws an exception or always loops forever.

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

A variable can be marked volatile, however their exact behaviour can be
further refined with four new aspects. Specifying only "Volatile" as in the
above example specifies all of the below aspects.

 * Async_Writers - This aspect only affects the proof system, which assumes
   that such an object can change at any point. An example of such a
   volatile object might be a temperature sensor: any two reads may yield a
   different result, but the mere act of reading does not otherwise affect
   the environment.

 * Effective_Reads - This aspect can only be specified on volatiles with
   Async_Writers, and only affects flow analysis. An example of such an a
   volatile object might be a network queue: any two reads may yield
   different results (as with Async_Writers), but any previous yield can
   have an effect on subsequent reads. Such a volatile can never be just an
   input, it must always be an in_out or output.

 * Async_Readers - This aspect currently has no effect on analysis, but
   serves a documentation purpose. It describes objects that are volatile,
   but their effects should not be modelled by SPARK.

 * Effective_Writes - This aspect can only be specified on volatiles with
   Async_Readers, and only affects flow analysis. This considers each write
   to have an effect. An example of such an object could be a stack: Each
   subsequent value pushed (written) to the stack is important, even if you
   push the same value twice.
