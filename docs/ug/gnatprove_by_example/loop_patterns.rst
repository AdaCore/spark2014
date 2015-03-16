Loop Patterns
-------------

As you gain experience in proving loops, you will find that you recognize
common *loop patterns*; you may recognize the code of loop bodies as well
as typical properties you want to prove for those loops, and the necessary
loop invariants. This section contains a collection of such commonly
occurring loop patterns. For each loop pattern we provide a brief
explanation followed by one or two examples. These loop patterns can be
used to minimize the time spent on loop proving. First we make a few notes
about loop patterns in general.

What Is the Proof Objective of Your Loop?
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The loop invariant and its complexity is greatly influenced by
the *proof objective of the loop*. When we say "proof objective of the
loop" this means the condition that needs to hold after the loop. If the
subprogram returns straight after the loop, then this is the same as the
postcondition of the subprogram. If there is some code in between the loop
and the end of the subprogram, then the "proof objective of the loop" is
the weakest precondition required for that code to ensure that the
postcondition of the subprogram holds.

Loop Pattern Granularity
^^^^^^^^^^^^^^^^^^^^^^^^

After studying some loop patterns, you will probably find patterns among
the loop patterns! In fact, all patterns described in this section can be
seen as instantiations of a very general loop pattern:

================  ========================
Loop Pattern      Loop Over Data Structure
================  ========================
Proof Objective   Establish property P.
Loop Behavior     Loops over the data structure and establishes P.
Loop Invariant    Property P is established for the part of the data structure
                  looped over so far.
================  ========================

However, it is useful to break this down into more detailed patterns since
often a small modification to the proof objective, or to the control
behavior of the loop, leads to a significantly changed loop invariant. In
the following, we focus on some loop patterns for scalar and array
properties that occur frequently in practice.

In the remainder of this section we identify the following loop
patterns:

#. :ref:`Initialization Patterns`

   a) default array initialization
   b) array initialization using dynamic expressions

#. :ref:`Validation Patterns`

   a) with early exit
   b) keep validating
   c) preserve flag

#. :ref:`Update Patterns`

   a) array update, basic
   b) array update, strong

#. :ref:`Search Patterns`

   a) linear
   b) binary

#. :ref:`Calculation Patterns`

   a) bounded summation

.. _Initialization Patterns:

Initialization Patterns
^^^^^^^^^^^^^^^^^^^^^^^

|

================  ========================
Loop Pattern      Array Initialization
================  ========================
Proof Objective   Every element of the array has a specific value.
Loop Behavior     Loops linearly over the array indexes and initializes every
                  element of the array.
                  The array to be initialized is an out parameter.
Loop Invariant    Every element initialized so far has its specific value.
================  ========================

Example: Default Array Initialization
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This example illustrates a common and basic form of array initialization
using a loop. The specification ``Init`` is given in the file
``init.ads``. Study the specification of the ``Default_Initialize``
subprogram, using the array type of ``Loop_Types``:

.. literalinclude:: loop_patterns/default_initialisation_flow/loop_types.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/default_initialisation_flow/init.ads
   :language: ada
   :linenos:

Note the typical proof objective of an array initialization in the
postcondition of ``Default_Initialize``. The implementation of
``Default_Initialize`` is given in the file ``init.adb``. Note the loop
invariant:

.. literalinclude:: loop_patterns/default_initialisation_flow/init.adb
   :language: ada
   :linenos:

The loop invariant follows the typical pattern of array initialization, and
is strong enough to prove that the loop fulfils the postcondition. We run
|GNATprove| with a prover timeout of 60 seconds (switch ``--timeout=60``)
and we have set the compiler flag to avoid intermediate overflows for
assertions (switch ``-gnato13``) to get the results presented throughout
this section. Inspection of the proof results confirms that the loop
invariant is correct; loop invariant initialization, loop invariant
preservation, as well as the postcondition, are all proved. However, we get
a few "medium" failed checks regarding initialization of the array ``A``:

.. literalinclude:: loop_patterns/results/default_initialisation_flow.prove
   :language: none
   :linenos:

Even though the proof of the loop is successful --- and this is our main
focus here --- |SPARK| static analysis has reported some flow
initialization issues. This particular case of flow analysis problem
is sufficiently common to justify a minor sidetrack here:

*Sidenote about flow analysis for array initialization:* Sometimes the
early (pre proof) |SPARK| static analysis step called *flow analysis*
produces false alarms about the possibility of an array not being entirely
initialized. This may be reported for example on access of an array element
inside a loop, or upon return of a subprogram with an out mode array
parameter. Proper initialization is required for sound proof, that is why
it is reported as a failed check. There are two ways to deal with these
false alarms about array initialization: 1) use an array aggregate for
initialization, or 2) justify the failed flow check using pragma
``Annotate``. Be careful to only justify a reported issue if you are
convinced that it is a false alarm! See :ref:`Data Initialization Policy`
for more details on this aspect of flow analysis.

For our default initialization example, after review of the loop code we
are convinced that this is a false alarm, and we put in the following two
justifications: Firstly, for the array access in the loop invariant in
the package body. Secondly, for the specification of
``Default_Initialize``:

.. literalinclude:: loop_patterns/default_initialisation_justified/init.adb
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/default_initialisation_justified/init.ads
   :language: ada
   :linenos:

Now, the flow analysis step is completed without failed checks and the
|SPARK| tools proceed with successful proof:

.. literalinclude:: loop_patterns/results/default_initialisation_justified.prove
   :language: none
   :linenos:

Example: Array Initialization using a Dynamic Expression
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Sometimes you want to initialize every element of an array using an
arbitrary dynamic expression, which is not known at compile time. Consider
a dynamic variant of our previous example, called ``Dynamic_Initialize``:

.. literalinclude:: loop_patterns/dynamic_initialisation/init.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/dynamic_initialisation/init.adb
   :language: ada
   :linenos:

Note here that the loop pattern is the same as for initialization using a
static value in the previous example. The new loop invariant and the proof
objective (in the post condition) still follow the pattern. There is a
notable difference in the program though: the precondition. Whenever you
calculate a dynamic expression, the precondition needs to be strong enough
to allow this calculation. Another difference is that this time we used an
array aggregate to create an initial "dummy" initialization which avoids any
flow array initilization checks to fail. We get the following proof
result:

.. literalinclude:: loop_patterns/results/dynamic_initialisation.prove
   :language: none
   :linenos:

.. _Validation Patterns:

Validation Patterns
^^^^^^^^^^^^^^^^^^^

Validation of sequences (arrays) is common in high integrity software. In
this section we will see how different proof objectives (or different loop
control flows) call for different patterns. First let us consider a
validation pattern where the loop terminates as soon as an invalid element
is encountered.

|

================  ========================
Loop Pattern      Sequence Validation with Early Exit
================  ========================
Proof Objective   Determine (flag) if there are any invalid elements in a given
                  array.
Loop Behavior     Loops linearly over the array elements and exits if an
                  invalid element is encountered.
Loop Invariant    Every element encountered so far is valid.
================  ========================

Example: Validate Sequence (Array)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: loop_patterns/validation_early_exit/validation.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/validation_early_exit/validation.adb
   :language: ada
   :linenos:

Note again how the post condition matches the proof objective of the loop
pattern, and the same for the loop invariant. We also get the expected
proof result:

.. literalinclude:: loop_patterns/results/validation_early_exit.prove
   :language: none
   :linenos:

|

===============  ===================================================
Loop Pattern     Sequence Validation that Validates Entire Structure
===============  ===================================================
Proof Objective  Determine (flag) if there are any invalid elements
                 in a given array.
Loop Behavior    Loops linearly over the array elements. If an invalid
                 element is encountered, flag this, but keep validating
                 (typically logging every invalidity) for the entire array.
Loop Invariant   If invalidity is not flagged, every element encountered so
                 far is valid.
===============  ===================================================

Note that even though we have the same proof objective (flag any
invalidity) as in the previous example, the control flow has changed not to
do early exit, and the loop invariant is different. The loop invariant of
the early exit pattern would be too strong and has been relaxed to an
implication.

Example: Validate Sequence, Keep Validating
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: loop_patterns/validation_keep_validating/validation.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/validation_keep_validating/validation.adb
   :language: ada
   :linenos:

As expected, we have successful proof results:

.. literalinclude:: loop_patterns/results/validation_keep_validating.prove
   :language: none
   :linenos:


|

===============  ==============================================
Loop Pattern     Sequence Validation Preserving Invalidity Flag
===============  ==============================================
Proof Objective  Determine (flag) if there are any invalid elements in
                 a given array, and preserve previously flagged alarm.
Loop Behavior    Loops linearly over the array elements. If an invalid
                 element is encountered, flag this, but keep validating
                 for the entire array and preserve previously flagged
                 alarm. The flag is an in out parameter.
Loop Invariant   If invalidity is not flagged, every element encountered
                 so far is valid. Preserve previously flagged alarm.
===============  ==============================================


A common usage pattern is to perform a sequence of validation operations,
for example at start-up, and collect all validation results in one flag:

.. code-block:: ada

  package body Startup
    with SPARK_Mode
  is
    procedure Initialize (Arr);

    procedure Do_Validation (Arr : in Arr_T; Success : out Boolean)
    is
    begin
      Success := True;

      Validate_This_Data (Arr, Success);

      Validate_That_Data (Arr, Success);

      Validate_This_Data_Too (Arr, Success);

    end Do_Validation;

end Startup;

Note here that the ``Success`` in out parameter is being used to pass on
previously flagged issues.

Example: Validate Sequence While Preserving Invalidity Flag
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The major difference from our earlier validation patterns is that this has
a stronger proof objective which also requires the program not to change
the in out alarm (Success) flag in an unsafe way.

.. literalinclude:: loop_patterns/validation_preserve_flag/validation.ads
   :language: ada
   :linenos:

The preservation of an alarm (``not Success``) is proved throughout the loop
using the ``'Loop_Entry`` attribute.

.. literalinclude:: loop_patterns/validation_preserve_flag/validation.adb
   :language: ada
   :linenos:

Again, we get successful proof result:

.. literalinclude:: loop_patterns/results/validation_preserve_flag.prove
   :language: none
   :linenos:


Example: Validate Sequence While Preserving Invalidity Flag --- Strong
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

So far we have seen validation patterns where the proof objective is
focused on safety properties. Safety properties are often formalised as an
implication that describes properties like "if no alarm is raised, then the
system is in a good state" or "if something bad happens, an alarm is
raised". These properties do not describe the entire functionality of the
subprogram, and can be fulfilled by overly "passive" programs for example a
program that does not do anything. Sometimes we want to make a full
function specification, and sometimes we work partially towards that goal,
to make a *stronger* proof objective.

|

================  ========================
Loop Pattern      Strong Sequence Validation Preserving Invalidity Flag
================  ========================
Proof Objective   The validity flag is True exactly when all the elements
                  are valid and previous validity was true.
Loop Behavior     Loops linearly over the array elements. If an invalid
                  element is encountered, flag this, but keep validating
                  for the entire array and preserve previously flagged
                  alarm. The flag is an in out parameter.
Loop Invariant    The validity flag is True exactly when all the elements
                  encountered so far are valid and previous validity was true.
================  ========================

.. literalinclude:: loop_patterns/validation_preserve_flag_strong/validation.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/validation_preserve_flag_strong/validation.adb
   :language: ada
   :linenos:

And the proof is successful:

.. literalinclude:: loop_patterns/results/validation_preserve_flag_strong.prove
   :language: none
   :linenos:

.. _Update Patterns:

Update Patterns
^^^^^^^^^^^^^^^

|

================  ========================
Loop Pattern      Array Update --- Basic
================  ========================
Proof Objective   Elements of the array are updated according to
                  specified positions and with specified component values.
Loop Behavior     Loops over (a range of) array elements and assigns the
                  specified positions to values.
Loop Invariant    Every element assigned so far has been assigned at the
                  specified position and value.
================  ========================

This is a commonly used pattern, where some elements in a data structure are
modified.

Example: Array Update --- Basic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: loop_patterns/updates/update.ads
   :language: ada
   :linenos:

Note how the post condition specifies the modified elements.

.. literalinclude:: loop_patterns/updates/update.adb
   :language: ada
   :linenos:

The loop invariant is a weakening of the postcondition, that the elemts
updates so far has the new vale. And the proof is successful:

.. literalinclude:: loop_patterns/results/updates.prove
   :language: none
   :linenos:

However, a call to the program that does not update any elements
(``First_Idx .. Last_Idx``) empty, would fulfil this post condition. Is that
the intention?

|

================  ========================
Loop Pattern      Array Update --- Strong
================  ========================
Proof Objective   Elements of the array are updated according to
                  specified positions and with specified component values.
                  Element not specified to be updated should have the same
                  value as on entry.
Loop Behavior     Loops over (a range of) array elements and assigns the
                  specified positions to values.
Loop Invariant    Every element assigned so far has been assigned at the
                  specified position and value. Element encountered so
                  far and not specified to be updated should have the same
                  value as on entry.
================  ========================

Example: Array Update --- Strong
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Sometimes we want to specify a stonger postcondition than the one we just
saw. This pattern is similar to the basic one but also requires all
elements that have not been specified to be updated, to remain the same:

.. literalinclude:: loop_patterns/updates_strong/update.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/updates_strong/update.adb
   :language: ada
   :linenos:

And the proof results:

.. literalinclude:: loop_patterns/results/updates_strong.prove
   :language: none
   :linenos:

.. _Search Patterns:

Search Patterns
^^^^^^^^^^^^^^^

We have seen earlier examples of linear and binary search, in the section
on :ref:`how to write loop invariants`.

|

================  ========================
Loop Pattern      Search with Early Exit
================  ========================
Proof Objective   Has found an element or position that meets a search
                  criterion.
Loop Behavior     Loops over the array elements. Exits when
                  found an element that meets the search criterion.
Loop Invariant    Every element encountered so far does not meet the search
                  criterion.
================  ========================

You may notice that this pattern has similarities with the validation
patterns. Together they can be called query patterns.

Example: Linear Wrap-Around Search of Table
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This time, let us make a slightly more complex example that searches for a
free slot over a table in a wrap-around fashion. This program uses two
consecutive loops, which illustrates that the "proof objective of the loop"
is not necessarily the same as the postcondition.

.. literalinclude:: loop_patterns/linear_search/find.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/linear_search/find.adb
   :language: ada
   :linenos:

And we get the following proof results:

.. literalinclude:: loop_patterns/results/linear_search.prove
   :language: none
   :linenos:


Example: Linear Wrap-around Search of Table --- Strong
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Similarly to what we did for the validation patterns, let us strengthen the
proof objective towards full functional behavior:

.. literalinclude:: loop_patterns/linear_search_strong/find.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/linear_search_strong/find.adb
   :language: ada
   :linenos:

Note that the proof objectives of the individual loops have not changed, but
the post condition that sums up the effects of the two loops has. We get
the following proof results:

.. literalinclude:: loop_patterns/results/linear_search_strong.prove
   :language: none
   :linenos:


Example: Binary Search SQRT
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This example uses binary search to find the interval of two consecutive
numbers squared, so that the given number lies therein. In every loop
iteration the search interval is halved and adjusted so that it gets
smaller while still containing the given number.

.. literalinclude:: loop_patterns/binary_search/sqrt.ads
   :language: ada
   :linenos:

The loop invariant states that for as much as the interval has been shrunk
so far, the given number lies therein.

.. literalinclude:: loop_patterns/binary_search/sqrt.adb
   :language: ada
   :linenos:

We get the following proof results:

.. literalinclude:: loop_patterns/results/binary_search.prove
   :language: none
   :linenos:

.. _Calculation Patterns:

Calculation Patterns
^^^^^^^^^^^^^^^^^^^^

|

================  ========================
Loop Pattern      Bounded Calculation
================  ========================
Proof Objective   Perform a calculation over all elements in a data structure
                  so that this is bounded.
Loop Behavior     Loops over the data structure, and uses the elements
                  to contribute to the calculated result.
Loop Invariant    The calculation performed so far is of a sufficiently small
                  bound so that the total bound can be met.
================  ========================

Example: Bounded Summation
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: loop_patterns/summation/summation.ads
   :language: ada
   :linenos:

Note that the precondition needs to be strong enough to ensure the total
bound can be met.

.. literalinclude:: loop_patterns/summation/summation.adb
   :language: ada
   :linenos:

Proof result:

.. literalinclude:: loop_patterns/results/summation.prove
   :language: none
   :linenos:

For more full-functional behavior specifications of calculations like
summation, usually lemmas or external axioms are necessary.
