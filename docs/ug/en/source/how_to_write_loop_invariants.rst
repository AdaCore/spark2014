.. _How to Write Loop Invariants:

How to Write Loop Invariants
============================

As described in :ref:`loop invariants`, proving properties of subprograms
that contain loops may require the addition of explicit loop
invariant contracts. This section describes a systematic approach
for writing loop invariants.

.. _Automatic Unrolling of Simple For-Loops:

Automatic Unrolling of Simple For-Loops
---------------------------------------

|GNATprove| automatically unrolls simple for-loops, defined as:

* for-loops over a range,
* with a number of iterations smaller than 20,
* without :ref:`loop invariants` or :ref:`loop variants`,
* that declare no local variables, or only variables of scalar type.

In addition, |GNATprove| always unrolls loops of the form ``for J in 1 .. 1
loop`` that don't have a :ref:`loop invariants` or :ref:`loop variants`, even
when they declare local variables of non-scalar type. This special form of loop
is used to simulate forward gotos by using exit statements instead.

As a result of unrolling, |GNATprove| conveys the exact meaning of the loop to
provers, without requiring a loop invariant. While this is quite powerful, it
is best applied to loops where the body of the loop is small, otherwise the
unrolling may lead to complex formulas that provers cannot prove.

For example, consider the subprograms ``Init`` and ``Sum`` below:

.. literalinclude:: /gnatprove_by_example/examples/loop_unrolling.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/loop_unrolling.adb
   :language: ada
   :linenos:

As the loops in both subprograms are simple for-loops, |GNATprove| unrolls them
and manages to prove the postconditions of ``Init`` and ``Sum`` without
requiring a loop invariant:

.. literalinclude:: /gnatprove_by_example/results/loop_unrolling.prove
   :language: none
   :linenos:

Automatic loop unrolling can be disabled locally by explicitly adding a default
loop invariant at the start of the loop:

.. code-block:: ada

   for X in A .. B loop
      pragma Loop_Invariant (True);
      ...
   end loop;

It can also be disabled globally by using the switch ``--no-loop-unrolling``.

.. _Automatically Generated Loop Invariants:

Automatically Generated Loop Invariants
---------------------------------------

In general, |GNATprove| relies on the user to manually supply the necessary
information about variables modified by loop statements in the loop invariant.
Though variables which are not modified in the loop need not be mentioned in
the invariant, it is usually necessary to state explicitly the preservation
of unmodified object parts, such as record or array components. In
particular, when a loop modifies a collection, which can be either an array or
a container (see :ref:`Formal Containers Library`), it may be necessary to
state in the loop invariant those parts of the collection that have not been
modified up to the current iteration. This property called `frame condition` in
the scientific literature is essential for |GNATprove|, which otherwise must
assume that all elements in the collection may have been modified. Special care
should be taken to write adequate frame conditions, as they usually look
obvious to programmers, and so it is very common to forget to write them and
not being able to realize what's the problem afterwards.

To alleviate this problem, the |GNATprove| tool generates automatically frame
conditions in some cases. As examples of use of such generated frame
conditions, consider the code of procedures ``Update_Arr`` and ``Update_Rec``
below:

.. literalinclude:: /gnatprove_by_example/examples/frame_condition.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/frame_condition.adb
   :language: ada
   :linenos:

Without this feature, |GNATprove| would not be able to prove the postconditions
of either procedure because:

* To prove the postcondition of ``Update_Arr``, one needs to know that only the
  indexes up to ``Idx`` have been updated in the loop.
* To prove the postcondition of ``Update_Rec``, one needs to know that only the
  component ``A`` of record ``R`` has been updated in the loop.

Thanks to this feature, |GNATprove| automatically proves the postconditions of
both procedures, without the need for loop invariants:

.. literalinclude:: /gnatprove_by_example/results/frame_condition.prove
   :language: none
   :linenos:

In particular, it is able to infer the preservation of
unmodified components of record variables. It also handles unmodified components of
array variables as long as they are preserved at every index in the array.
As an example, consider the following loop which only updates some record
component of a nested data structure:

.. literalinclude:: /gnatprove_by_example/examples/preserved_fields.adb
   :language: ada
   :linenos:

Despite the absence of a loop invariant in the above code,
|GNATprove| is able to prove that the assertions on lines 19-21 about variable
``D`` which is modified in the loop are proved, thanks to the generated loop
invariants:

.. literalinclude:: /gnatprove_by_example/results/preserved_fields.prove
   :language: none
   :linenos:

Note that |GNATprove| will not generate a frame condition for a record component if
the record variable is modified as a whole either through an assignment or
through a procedure call, et cetera, even if the component happens to be preserved
by the modification.

|GNATprove| can also infer preservation of unmodified array components for arrays
that are only updated at constant indexes or at indexes equal to the loop index.
As an example, consider the following loops, only updating some cells of a
matrix of arrays:

.. literalinclude:: /gnatprove_by_example/examples/preserved_components.adb
   :language: ada
   :linenos:

Despite the absence of a loop invariant in the above code,
|GNATprove| can succesfully verify the assertion on line 13 thanks to the
generated loop invariant. Note that loop invariant generation for preserved
array components is based on heuristics, and that it is therefore far from
complete. In particular, it does not handle updates to variable indexes different
from the loop index, as can be seen by the failed attempt to verify the
assertion on line 22. |GNATprove| does not either handle dependences between
indexes in an update, resulting in the failed attempt to verify the
assertion on line 33:

.. literalinclude:: /gnatprove_by_example/results/preserved_components.prove
   :language: none
   :linenos:

The Four Properties of a Good Loop Invariant
--------------------------------------------

A loop invariant can describe more or less precisely the behavior of a
loop. What matters is that the loop invariant allows proving absence of
run-time errors in the subprogram, that the subprogram respects its contract,
and that the loop invariant itself holds at each iteration of the loop. There
are four properties that a good loop invariant should fulfill:

#. [INIT] It should be provable in the first iteration of the loop.

#. [INSIDE] It should allow proving absence of run-time errors and local
   assertions inside the loop.

#. [AFTER] It should allow proving absence of run-time errors, local assertions
   and the subprogram postcondition after the loop.

#. [PRESERVE] It should be provable after the first iteration of the loop.

As a first example, here is a variant of the search algorithm described in
:ref:`spark tutorial`, which returns whether a collection contains a desired
value, and if so, at which index. The collection is implemented as an array.

The specification of ``Linear_Search`` is given in file ``linear_search.ads``.
The postcondition of ``Search`` expresses that, either the search returns a
result within the array bounds, in which case it is the desired index,
otherwise the array does not contain the value searched.

.. literalinclude:: /examples/linear_search_final/linear_search.ads
   :language: ada
   :linenos:

The implementation of ``Linear_Search`` is given in file ``linear_search.adb``.
The loop invariant of ``Search`` expresses that, at the end of each iteration,
if the loop has not been exited before, then the value searched is not in the
range of indexes between the start of the array ``A'First`` and the current
index ``Pos``.

.. literalinclude:: /examples/linear_search_final/linear_search.adb
   :language: ada
   :linenos:

With this loop invariant, |GNATprove| is able to prove all checks in
``Linear_Search``, both those related to absence of run-time errors and those
related to verification of contracts:

.. literalinclude:: /examples/results/linear_search_final.prove
   :language: none
   :linenos:

In particular, the loop invariant fulfills all four properties that we listed
above:

#. [INIT] It is proved in the first iteration (message on line 2).
#. [INSIDE] It allows proving absence of run-time errors inside the loop
   (messages on lines 1 and 4).
#. [AFTER] It allows proving absence of run-time errors after the loop
   (messages on lines 6 and 7) and the subprogram postcondition (message on
   line 5).
#. [PRESERVE] It is proved after the first iteration (message on line 3).

Note that the loop invariant closely resembles the second line in the
postcondition of the subprogram, except with a different range of values in the
quantification: instead of stating a property for all indexes in the array
``A``, the loop invariant states the same property for all indexes up to the
current loop index ``Pos``. In fact, if we equate ``Pos`` to ``A'Last`` for the
last iteration of the loop, the two properties are equal. This explains here
how the loop invariant allows proving the subprogram postcondition when the
value searched is not found.

Note also that we chose to put the loop invariant at the end of the loop. We
could as easily put it at the start of the loop. In that case, the range of
values in the quantification should be modified to state that, at the start of
each iteration, if the loop has not been exited before, then the value searched
is not in the range of indexes between the start of the array ``A'First`` and
the current index ``Pos`` *excluded*:

.. code-block:: ada

         pragma Loop_Invariant (for all K in A'First .. Pos - 1 => A (K) /= I);

Indeed, the test for the value at index ``Pos`` is done after the loop
invariant in that case.

We will now demonstrate techniques to complete a loop invariant so that it
fulfills all four properties [INIT], [INSIDE], [AFTER] and [PRESERVE], on a
more complex algorithm searching in an ordered collection of elements. Like the
naive search algorithm just described, this algorithm returns whether the
collection contains the desired value, and if so, at which index. The
collection is also implemented as an array.

The specification of this ``Binary_Search`` is given in file ``binary_search.ads``:

.. literalinclude:: /examples/binary_search_no_loopinv/binary_search.ads
   :language: ada
   :linenos:

The implementation of ``Binary_Search`` is given in file ``binary_search.adb``:

.. literalinclude:: /examples/binary_search_no_loopinv/binary_search.adb
   :language: ada
   :linenos:

Note that, although function ``Search`` has a loop, we have not given an
explicit loop invariant yet, so the default loop invariant of ``True`` will be
used by |GNATprove|. We are running |GNATprove| with a prover timeout of 60 seconds
(switch ``--timeout=60``) to get the results presented in the rest of this
section.

Proving a Loop Invariant in the First Iteration
-----------------------------------------------

Property [INIT] is the easiest one to prove. This is equivalent to proving a
pragma Assert in the sequence of statements obtained by unrolling the loop
once. In particular, if the loop invariant is at the start of the loop, this is
equivalent to proving a pragma Assert just before the loop. Therefore, the
usual techniques for investigating unproved checks apply, see :ref:`how to
investigate unproved checks`.

Completing a Loop Invariant to Prove Checks Inside the Loop
-----------------------------------------------------------

Let's start by running |GNATprove| on program ``Binary_Search`` without loop
invariant. It generates two medium messages, one corresponding to a possible
run-time check failure, and one corresponding to a possible failure of
the postcondition:

.. literalinclude:: /examples/results/binary_search_no_loopinv.prove
   :language: none

We will focus here on the message inside the loop, which corresponds to
property [INSIDE]. The problem is that variable ``Med`` varies in the loop, so
|GNATprove| only knows that its value is in the range of its type ``Index`` at
the start of an iteration (line 23), and that it is then assigned the value of
``Left + (Right - Left) / 2`` (line 24) before being used as an index into
array ``A`` (lines 26 and 28) and inside expressions assigned to ``Left`` and
``Right`` (lines 27 and 29).

As ``Left`` and ``Right`` also vary in the loop, |GNATprove| cannot use the
assignment on line 24 to compute a more precise range for variable ``Med``,
hence the message on index check.

What is needed here is a loop invariant that states that the values of ``Left``
and ``Right`` stay within the bounds of ``A`` inside the loop:

.. literalinclude:: /examples/binary_search_range/binary_search.adb
   :language: ada
   :lines: 23-26

With this simple loop invariant, |GNATprove| now reports that the
check on line 26 is proved.
|GNATprove| computes that the value assigned to ``Med`` in the loop is also
within the bounds of ``A``.

Completing a Loop Invariant to Prove Checks After the Loop
----------------------------------------------------------

With the simple loop invariant given before, |GNATprove| still reports that the
postcondition of ``Search`` may fail, which corresponds to property [AFTER]. By
instructing |GNATprove| to prove checks progressively, as seens in
:ref:`proving spark programs`, we even get a precise message pointing to the
part of the postcondition that could not be proved:

.. literalinclude:: /examples/results/binary_search_range.prove
   :language: none

Here, the message shows that the second line of the postcondition could not be
proved. This line expresses that, in the case where ``Search`` returns
``No_Index`` after the loop, the array ``A`` should not contain the value
searched ``I``.

One can very easily check that, if |GNATprove| can prove this property, it can
also prove the postcondition. Simply insert a pragma Assert after the loop
stating this property:

.. literalinclude:: /examples/binary_search_post_assert/binary_search.adb
   :language: ada
   :lines: 35-38

|GNATprove| now succeeds in proving the postcondition, but it fails to prove
the assertion:

.. literalinclude:: /examples/results/binary_search_post_assert.prove
   :language: none

The problem is that |GNATprove| only knows what the user specified about ``A``
in the precondition, namely that it is sorted in ascending order. Nowhere it is
said that ``A`` does not contain the value ``I``. Note that adding this
assertion is not compulsory. It simply helps identifying what is needed to
achieve property [AFTER], but it can be removed afterwards.

What is needed here is a loop invariant stating that, if ``A`` contains the
value ``I``, it must be at an index in the range ``Left..Right``, so when the
loop exits because ``Left > Right`` (so the loop test becomes false), ``A``
cannot contain the value ``I``.

One way to express this property is to state that the value of ``A`` at
index ``Left - 1`` is less than ``I``, while the value of ``A`` at index
``Right + 1`` is greater than ``I``. Taking into account the possibility that
there are no such indexes in ``A`` if either ``Left`` or ``Right`` are at the
boundaries of the array, we can express it as follows:

.. literalinclude:: /examples/binary_search_naive/binary_search.adb
   :language: ada
   :lines: 23-28

|GNATprove| manages to prove these additional loop invariants, but it still
cannot prove the assertion after the loop. The reason is both simple and
far-reaching. Although the above loop invariant together with the property that
the array is sorted imply the property we want to express, it still requires
additional work for the prover to reach the same conclusion, which may prevent
automatic proof in the allocated time. In that case, it is better to express
the equivalent but more explicit property directly, as follows:

.. literalinclude:: /examples/binary_search_precise/binary_search.adb
   :language: ada
   :lines: 23-31

|GNATprove| now proves the assertion after the loop. In general, it is simpler
to understand the relationship between the loop invariant and the checks that
follow the loop when the loop invariant is directly followed by the exit
statement that controls loop termination. In a "for" or "while" loop, this can
mean it is easier to place the Loop_Invariant pragmas at the *end* of the loop
body, where they precede the (implicit) exit statement.  In such cases, the loop
invariant is more likely to resemble the postcondition.

Proving a Loop Invariant After the First Iteration
--------------------------------------------------

With the loop invariant given before, |GNATprove| also proves that the loop
invariant of ``Search`` holds after the first iteration, which corresponds to
property [PRESERVE]. In fact, we have now arrived at a loop invariant which
allows |GNATprove| to prove all checks for subprogram ``Search``.

This is not always the case. In general, when the loop invariant is not proved
after the first iteration, the problem is that the loop invariant is not
precise enough. The only information that |GNATprove| knows about the value of
variables that are modified in the loop, at each loop iteration, is the
information provided in the loop invariant. If the loop invariant is missing
some crucial information about these variables, which is needed to prove the
loop invariant after N iterations, |GNATprove| won't be able to prove that the
loop invariant holds at each iteration.

In loops that modify variables of composite types (records and arrays), it is
usually necessary at this stage to add in the loop invariant some information
about those parts of the modified variables which are not modified by the loop,
or which are not modified in the first N iterations of the loop. Otherwise,
|GNATprove| assumes that these parts may also be modified, which can prevent it
from proving the preservation of the loop invariant. See :ref:`loop invariants`
for an example where this is needed.

In other cases, it may be necessary to guide the prover with intermediate
assertions. A rule of thumb for deciding which properties to assert, and where
to assert them, is to try to locate at which program point the prover does not
success in proving the property of interest, and to restate other properties
that are useful for the proof.

In yet other cases, where the difficulty is related to the size of the loop
rather than the complexity of the properties, it may be useful to factor the
loop into into local subprograms so that the subprograms' preconditions and
postconditions provide the intermediate assertions that are needed to prove the
loop invariant.
