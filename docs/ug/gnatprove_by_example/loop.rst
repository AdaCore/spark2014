Loop Examples
-------------

The examples in this section contain loops, and thus require in general that
users write suitable :ref:`Loop Invariants`. We start by explaining the need
for a loop invariant, and we continue with a description of the most common
patterns of loops and their loop invariant. We summarize each pattern in a
table of the following form:

 ================  ========================
 Loop Pattern      Loop Over Data Structure
 ================  ========================
 Proof Objective   Establish property P.
 Loop Behavior     Loops over the data structure and establishes P.
 Loop Invariant    Property P is established for the part of the data structure
                   looped over so far.
 ================  ========================

The examples in this section use the types defined in package ``Loop_Types``:

.. literalinclude:: gnatprove_by_example/examples/loop_types.ads
   :language: ada
   :linenos:

The Need for a Loop Invariant
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Consider a simple procedure that increments its integer parameter ``X`` a
number ``N`` of times:

.. literalinclude:: gnatprove_by_example/examples/increment_loop.adb
   :language: ada
   :linenos:

The precondition of ``Increment_Loop`` ensures that there is no overflow when
incrementing ``X`` in the loop, and its postcondition states that ``X`` has
been incremented ``N`` times. This contract is a generalization of the contract
given for a single increment in :ref:`Increment`. |GNATprove| does not manage
to prove either the absence of overflow or the postcondition of
``Increment_Loop``:

.. literalinclude:: gnatprove_by_example/results/increment_loop.prove
   :language: none

As described in :ref:`How to Write Loop Invariants`, this is because variable
``X`` is modified in the loop, hence |GNATprove| knows nothing about it unless
it is stated in a loop invariant. If we add such a loop invariant that
describes precisely the value of ``X`` in each iteration of the loop:

.. literalinclude:: gnatprove_by_example/examples/increment_loop_inv.adb
   :language: ada
   :linenos:

then |GNATprove| proves both the absence of overflow and the postcondition of
``Increment_Loop_Inv``:

.. literalinclude:: gnatprove_by_example/results/increment_loop_inv.prove
   :language: none

Fortunately, many loops fall into some broad categories for which the loop
invariant is known. In the following sections, we describe these common
patterns of loops and their loop invariant, which involve in general iterating
over the content of a collection (either an array or a container from the
:ref:`Formal Containers Library`).

.. _Initialization Loops:

Initialization Loops
^^^^^^^^^^^^^^^^^^^^

This kind of loops iterates over a collection to initialize every element of
the collection to a given value:

 ================  ========================
 Loop Pattern      Separate Initialization of Each Element
 ================  ========================
 Proof Objective   Every element of the collection has a specific value.
 Loop Behavior     Loops over the collection and initializes every
                   element of the collection.
 Loop Invariant    Every element initialized so far has its specific value.
 ================  ========================

In the simplest case, every element is assigned the same value. For example, in
procedure ``Init_Arr_Zero`` below, value zero is assigned to every element of
array ``A``:

.. literalinclude:: gnatprove_by_example/examples/init_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have the value zero. With this loop invariant, |GNATprove| is able to
prove the postcondition of ``Init_Arr_Zero``, namely that all elements of the
array have value zero:

.. literalinclude:: gnatprove_by_example/results/init_arr_zero.prove
   :language: none

.. note::

   Pragma Annotate is used in ``Init_Arr_Zero`` to justify a message issued by
   flow analysis, about the possible read of uninitialized value ``A(K)`` in
   the loop invariant. Indeed, flow analysis is not currently able to infer
   that all elements up to the loop index ``J`` have been initialized, hence it
   issues a message that ``"A" might not be initialized``. For more details,
   see section on :ref:`Justifying Check Messages`.

Consider now a variant of the same initialization loop over a vector:

.. literalinclude:: gnatprove_by_example/examples/init_vec_zero.adb
   :language: ada
   :linenos:

Like before, the loop invariant expresses that all elements up to the current
loop index ``J`` have the value zero. Another loop invariant is needed here to
express that the length of the vector does not change in the loop: as variable
``V`` is modified in the loop, |GNATprove| does not know its length stays the
same (for example, calling procedure ``Append`` or ``Delete_Last`` would change
this length) unless the user says so in the loop invariant. This is different
from arrays whose length cannot change. With this loop invariant, |GNATprove|
is able to prove the postcondition of ``Init_Vec_Zero``, namely that all
elements of the vector have value zero:

.. literalinclude:: gnatprove_by_example/results/init_vec_zero.prove
   :language: none

Similarly, consider a variant of the same initialization loop over a list:

.. literalinclude:: gnatprove_by_example/examples/init_list_zero.adb
   :language: ada
   :linenos:

Contrary to arrays and vectors, lists are not indexed. Instead, a cursor can be
defined to iterate over the list. The loop invariant expresses that all
elements up to the current cursor ``Cu`` have the value zero. Contrary to the
case of vectors, no loop invariant is needed to express that the length of the
list does not change in the loop, because the postcondition remains provable
here even if the length of the list changes. With this loop invariant,
|GNATprove| is able to prove the postcondition of ``Init_List_Zero``, namely
that all elements of the list have value zero:

.. literalinclude:: gnatprove_by_example/results/init_list_zero.prove
   :language: none

The case of sets and maps is similar to the case of lists.

.. note::

   The parameter of ``Init_Vec_Zero`` and ``Init_List_Zero`` is an in out
   parameter. This is because some components of the vector/list parameter are
   preserved by the initialization procedure (in particular the component
   corresponding to its length). This is different from ``Init_Arr_Zero`` which
   takes an out parameter, as all components of the array are initialized by
   the procedure (the bounds of an array are not modifiable, hence considered
   separately from the parameter mode).

Consider now a case where the value assigned to each element is not the
same. For example, in procedure ``Init_Arr_Index`` below, each element of array
``A`` is assigned the value of its index:

.. literalinclude:: gnatprove_by_example/examples/init_arr_index.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have the value of their index. With this loop invariant, |GNATprove| is
able to prove the postcondition of ``Init_Arr_Index``, namely that all elements
of the array have the value of their index:

.. literalinclude:: gnatprove_by_example/results/init_arr_index.prove
   :language: none

Similarly, variants of ``Init_Vec_Zero`` and ``Init_List_Zero`` that assign a
different value to each element of the collection would be proved by
|GNATprove|.

.. _Validation Loops:

Validation Loops
^^^^^^^^^^^^^^^^

This kind of loops iterates over a collection to validate that every element of
the collection has a valid value. The most common pattern is to exit or return
from the loop if an invalid value if encountered:

 ================  ========================
 Loop Pattern      Sequence Validation with Early Exit
 ================  ========================
 Proof Objective   Determine (flag) if there are any invalid elements in a given
                   collection.
 Loop Behavior     Loops over the collection and exits/returns if an
                   invalid element is encountered.
 Loop Invariant    Every element encountered so far is valid.
 ================  ========================

Consider a procedure ``Validate_Arr_Zero`` that checks that all elements of an
array ``A`` have value zero:

.. literalinclude:: gnatprove_by_example/examples/validate_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have value zero. With this loop invariant, |GNATprove| is able to prove
the postcondition of ``Validate_Arr_Zero``, namely that output parameter
``Success`` is True if-and-only-if all elements of the array have value zero:

.. literalinclude:: gnatprove_by_example/results/validate_arr_zero.prove
   :language: none

Consider now a variant of the same validation loop over a vector:

.. literalinclude:: gnatprove_by_example/examples/validate_vec_zero.adb
   :language: ada
   :linenos:

Like before, the loop invariant expresses that all elements up to the current
loop index ``J`` have the value zero. Since variable ``V`` is not modified in
the loop, no additional loop invariant is needed here for |GNATprove| to know
that its length stays the same (this is different from the case of
``Init_Vec_Zero`` seen previously). With this loop invariant, |GNATprove| is
able to prove the postcondition of ``Validate_Vec_Zero``, namely that output
parameter ``Success`` is True if-and-only-if all elements of the vector have
value zero:

.. literalinclude:: gnatprove_by_example/results/validate_vec_zero.prove
   :language: none

Similarly, consider a variant of the same validation loop over a list:

.. literalinclude:: gnatprove_by_example/examples/validate_list_zero.adb
   :language: ada
   :linenos:

Like in the case of ``Init_List_Zero`` seen previously, we need to define a
cursor here to iterate over the list. The loop invariant expresses that all
elements up to the current cursor ``Cu`` have the value zero. With this loop
invariant, |GNATprove| is able to prove the postcondition of
``Validate_List_Zero``, namely that output parameter ``Success`` is True
if-and-only-if all elements of the list have value zero:

.. literalinclude:: gnatprove_by_example/results/validate_list_zero.prove
   :language: none

The case of sets and maps is similar to the case of lists.

A variant of the previous validation pattern is to continue validating elements
even after an invalid value has been encountered, which allows for example
logging all invalid values:

 ===============  ===================================================
 Loop Pattern     Sequence Validation that Validates Entire Collection
 ===============  ===================================================
 Proof Objective  Determine (flag) if there are any invalid elements
                  in a given collection.
 Loop Behavior    Loops over the collection. If an invalid
                  element is encountered, flag this, but keep validating
                  (typically logging every invalidity) for the entire collection.
 Loop Invariant   If invalidity is not flagged, every element encountered so
                  far is valid.
 ===============  ===================================================

Consider a variant of ``Validate_Arr_Zero`` that keeps validating elements of
the array after a non-zero element has been encountered:

.. literalinclude:: gnatprove_by_example/examples/validate_full_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant has been modified to state that all elements up to the
current loop index J have value zero if-and-only-if the output parameter
Success is True. This in turn requires to move the assignment of ``Success``
before the loop. With this loop invariant, |GNATprove| is able to prove the
postcondition of ``Validate_Full_Arr_Zero``, which is the same as the
postcondition of ``Validate_Arr_Zero``, namely that output parameter
``Success`` is True if-and-only-if all elements of the array have value zero:

.. literalinclude:: gnatprove_by_example/results/validate_full_arr_zero.prove
   :language: none

Similarly, variants of ``Validate_Vec_Zero`` and ``Validate_List_Zero`` that
keep validating elements of the collection after a non-zero element has been
encountered would be proved by |GNATprove|.

.. _Search Loops:

Search Loops
^^^^^^^^^^^^

This kind of loops iterates over a collection to search an element of the
collection that meets a given search criterion:

 ================  ========================
 Loop Pattern      Search with Early Exit
 ================  ========================
 Proof Objective   Find an element or position that meets a search
                   criterion.
 Loop Behavior     Loops over the collection. Exits when an
                   element that meets the search criterion is found.
 Loop Invariant    Every element encountered so far does not meet the search
                   criterion.
 ================  ========================

Consider a procedure ``Search_Arr_Zero`` that searches an element with value
zero in array ``A``:

.. literalinclude:: gnatprove_by_example/examples/search_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have a non-zero value. With this loop invariant, |GNATprove| is able to
prove the postcondition of ``Search_Arr_Zero``, namely that output parameter
``Success`` is True if-and-only-if there is an element of the array that has
value zero, and that ``Pos`` is the index of such an element:

.. literalinclude:: gnatprove_by_example/results/search_arr_zero.prove
   :language: none

Consider now a variant of the same search loop over a vector:

.. literalinclude:: gnatprove_by_example/examples/search_vec_zero.adb
   :language: ada
   :linenos:

Like before, the loop invariant expresses that all elements up to the current
loop index ``J`` have a non-zero value. With this loop invariant, |GNATprove|
is able to prove the postcondition of ``Search_Vec_Zero``, namely that output
parameter ``Success`` is True if-and-only-if there is an element of the vector
that has value zero, and that ``Pos`` is the index of such an element:

.. literalinclude:: gnatprove_by_example/results/search_vec_zero.prove
   :language: none

Similarly, consider a variant of the same search loop over a list:

.. literalinclude:: gnatprove_by_example/examples/search_list_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current cursor ``Cu``
have a non-zero value. With this loop invariant, |GNATprove| is able to prove
the postcondition of ``Search_List_Zero``, namely that output parameter
``Success`` is True if-and-only-if there is an element of the list that has
value zero, and that ``Pos`` is the cursor of such an element:

.. literalinclude:: gnatprove_by_example/results/search_list_zero.prove
   :language: none

The case of sets and maps is similar to the case of lists. For more complex
examples of search loops, see the :ref:`SPARK Tutorial` as well as the section
on :ref:`How to Write Loop Invariants`.

.. _Update Loops:

Update Loops
^^^^^^^^^^^^

This kind of loops iterates over a collection to update individual elements
based either on their value or on their position. The first pattern we consider
is the one that updates elements based on their value:

 ================  ========================
 Loop Pattern      Modification of Elements Based on Value
 ================  ========================
 Proof Objective   Elements of the collection are updated based on their value.
 Loop Behavior     Loops over a collection and assigns the elements whose value satisfies
                   a given modification criterion.
 Loop Invariant    Every element encountered so far has been assigned according to its value.
 ================  ========================

Consider a procedure ``Update_Arr_Zero`` that sets to zero all elements in
array ``A`` that have a value smaller than a given ``Threshold``:

.. literalinclude:: gnatprove_by_example/examples/update_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have been zeroed out if initially smaller than ``Threshold``, and that
elements that follow the current loop index have not been modified. With this
loop invariant, |GNATprove| is able to prove the postcondition of
``Update_Arr_Zero``, namely that all elements initially smaller than
``Threshold`` have been zeroed out, and that other elements have not been
modified:

.. literalinclude:: gnatprove_by_example/results/update_arr_zero.prove
   :language: none

Consider now a variant of the same update loop over a vector:

.. literalinclude:: gnatprove_by_example/examples/update_vec_zero.adb
   :language: ada
   :linenos:

Expressing the same postcondition as on ``Update_Arr_Zero`` would require using
``V'Old`` which is not possible because the vector type is limited. Hence, we
state a weaker postcondition here, namely that all elements of the vector are
either zero or greater than ``Threshold`` on return. The loop invariant
expresses that all elements up to the current loop index ``J`` are either zero
or greater than ``Threshold``, and that the length of ``V`` is not modified
(like in ``Init_Vec_Zero``). With this loop invariant, |GNATprove| is able to
prove the postcondition of ``Update_Vec_Zero``:

.. literalinclude:: gnatprove_by_example/results/update_vec_zero.prove
   :language: none

We don't show here a variant of the same update loop over a list, which
requires more involved postconditions and loop invariants, and is not proved
completely with the default provers Alt-Ergo and CVC4.

..
   THIS IS COMMENTED AS CURRENTLY GNATPROVE DOES NOT PROVE MANY CHECKS ON THAT CODE

   Similarly, consider a variant of the same update loop over a list:

   .. literalinclude:: gnatprove_by_example/examples/update_list_zero.adb
      :language: ada
      :linenos:

   The loop invariant expresses that all elements up to the current cursor ``Cu``
   have been zeroed out if initially smaller than ``Threshold`` (using function
   ``First_To_Previous`` to retrieve the part of the list up to the current
   cursor), and that elements that follow the current loop index have not been
   modified (using function ``Current_To_Last`` to retrieve the part of the list
   following the current cursor). With this loop invariant, |GNATprove| is able to
   prove the postcondition of ``Update_List_Zero``, namely that all elements
   initially smaller than ``Threshold`` have been zeroed out, and that other
   elements have not been modified:

   .. literalinclude:: gnatprove_by_example/results/update_list_zero.prove
      :language: none

   The case of sets and maps is similar to the case of lists.

The second pattern of update loops that we consider now is the one that updates
elements based on their position:

 ================  ========================
 Loop Pattern      Modification of Elements Based on Position
 ================  ========================
 Proof Objective   Elements of the collection are updated based on their position.
 Loop Behavior     Loops over a collection and assigns the elements whose position satisfies
                   a given modification criterion.
 Loop Invariant    Every element encountered so far has been assigned according to its position.
 ================  ========================

Consider a procedure ``Update_Range_Arr_Zero`` that sets to zero all elements
in array ``A`` between indexes ``First`` and ``Last``:

.. literalinclude:: gnatprove_by_example/examples/update_range_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements between ``First`` and the
current loop index ``J`` have been zeroed out, and that other elements have not
been modified (using :ref:`Attribute Update` to express this concisely). With
this loop invariant, |GNATprove| is able to prove the postcondition of
``Update_Range_Arr_Zero``, namely that all elements between ``First`` and
``Last`` have been zeroed out, and that other elements have not been modified
(using a combination of :ref:`Attribute Old` and :ref:`Attribute Update`):

.. literalinclude:: gnatprove_by_example/results/update_range_arr_zero.prove
   :language: none

Consider now a variant of the same update loop over a vector:

.. literalinclude:: gnatprove_by_example/examples/update_range_vec_zero.adb
   :language: ada
   :linenos:

For the same reason of vector type being limited that we explained on
``Update_Vec_Zero``, we state a weaker postcondition for
``Update_Range_Vec_Zero`` than for ``Update_Range_Arr_Zero``, namely that all
elements of the vector between ``First`` and ``Last`` have been zeroed out. The
loop invariant expresses all elements between ``First`` and ``J`` have been
zeroed out, and that the length of ``V`` is not modified (like in
``Init_Vec_Zero``). With this loop invariant, |GNATprove| is able to prove the
postcondition of ``Update_Range_Vec_Zero``:

.. literalinclude:: gnatprove_by_example/results/update_range_vec_zero.prove
   :language: none

We don't show here a variant of the same update loop over a list, which
requires more involved postconditions and loop invariants, and is not proved
completely with the default provers Alt-Ergo and CVC4.
