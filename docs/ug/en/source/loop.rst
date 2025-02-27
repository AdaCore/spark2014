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

.. literalinclude:: /examples/ug__loop_types/loop_types.ads
   :language: ada
   :linenos:

As there is no built-in way to iterate over the elements of a recursive
data structure, the first function ``For_All_List`` can be used to state that
all elements of a list have a given property. The second variant of
``For_All_List`` takes two lists and states that both lists have the same number
of elements and that the corresponding elements of both lists are related by the
given relation. The function ``At_End`` is used to
refer to the value of a borrowed list or a local borrower at the end of the
borrow, see :ref:`Referring to a value at the end of a borrow` for more
explanations.

.. note::
   Although the structural subprogram variant of ``For_All_List`` is proved,
   this is not sufficient to prove the termination of ``For_All_List``,
   as we have no way for now to state on
   the access-to-subprogram type Property that all elements of this type
   must terminate. Therefore, we justify this check, see section on
   :ref:`Justifying Check Messages`.

.. index:: Loop_Invariant; rationale

The Need for a Loop Invariant
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Consider a simple procedure that increments its integer parameter ``X`` a
number ``N`` of times:

.. literalinclude:: /examples/ug__increment_loop/increment_loop.adb
   :language: ada
   :linenos:

The precondition of ``Increment_Loop`` ensures that there is no overflow when
incrementing ``X`` in the loop, and its postcondition states that ``X`` has
been incremented ``N`` times. This contract is a generalization of the contract
given for a single increment in :ref:`Increment`. |GNATprove| does not manage
to prove either the absence of overflow or the postcondition of
``Increment_Loop``:

.. literalinclude:: /examples/ug__increment_loop/test.out
   :language: none

As described in :ref:`How to Write Loop Invariants`, this is because variable
``X`` is modified in the loop, hence |GNATprove| knows nothing about it unless
it is stated in a loop invariant. If we add such a loop invariant, as suggested
by the possible explanation in the message issued by |GNATprove|, that
describes precisely the value of ``X`` in each iteration of the loop:

.. literalinclude:: /examples/ug__increment_loop_inv/increment_loop_inv.adb
   :language: ada
   :linenos:

then |GNATprove| proves both the absence of overflow and the postcondition of
``Increment_Loop_Inv``:

.. literalinclude:: /examples/ug__increment_loop_inv/test.out
   :language: none

Fortunately, many loops fall into some broad categories for which the loop
invariant is known. In the following sections, we describe these common
patterns of loops and their loop invariant, which involve in general iterating
over the content of a collection (either an array, a container from the
:ref:`Formal Containers Library`, or a pointer-based linked list).

.. index:: Loop_Invariant; initialization loops

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

.. literalinclude:: /examples/ug__init_arr_zero/init_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have the value zero. With this loop invariant, |GNATprove| is able to
prove the postcondition of ``Init_Arr_Zero``, namely that all elements of the
array have value zero:

.. literalinclude:: /examples/ug__init_arr_zero/test.out
   :language: none

In the example above, pragma Annotate is used in ``Init_Arr_Zero`` to justify
a message issued by flow analysis, about the possible read of uninitialized
value ``A(K)`` in the loop invariant. Indeed, flow analysis is not currently
able to infer that all elements up to the loop index ``J`` have been
initialized, hence it issues a message that ``"A" might not be initialized``.
For more details, see section on :ref:`Justifying Check Messages`.

To verify this loop completely, it is possible to annotate ``A`` with the
Relaxed_Initialization aspect to use proof to verify its correct initialization
(see :ref:`Aspect Relaxed_Initialization` for more details).
In this case, the loop invariant should be extended to state that the elements
of ``A`` have been initialized by the loop up to the current index:

.. literalinclude:: /examples/ug__init_arr_zero_relaxed_init/init_arr_zero.adb
   :language: ada
   :linenos:

Remark that the postcondition of ``Init_Arr_Zero`` also needs to state that
``A`` is entirely initialized by the call.

Consider now a variant of the same initialization loop over a vector:

.. literalinclude:: /examples/ug__init_vec_zero/init_vec_zero.adb
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

.. literalinclude:: /examples/ug__init_vec_zero/test.out
   :language: none

Similarly, consider a variant of the same initialization loop over a list:

.. literalinclude:: /examples/ug__init_list_zero/init_list_zero.adb
   :language: ada
   :linenos:

Contrary to arrays and vectors, lists are not indexed. Instead, a cursor can be
defined to iterate over the list. The loop invariant expresses that all
elements up to the current cursor ``Cu`` have the value zero. To access the
element stored at a given position in a list, we use the function ``Model``
which computes the mathematical sequence of the elements stored in the list.
The position of a cursor in this sequence is retrieved using the ``Positions``
function. Contrary to the
case of vectors, no loop invariant is needed to express that the length of the
list does not change in the loop, because the postcondition remains provable
here even if the length of the list changes. With this loop invariant,
|GNATprove| is able to prove the postcondition of ``Init_List_Zero``, namely
that all elements of the list have value zero:

.. literalinclude:: /examples/ug__init_list_zero/test.out
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

Consider now a variant of the same initialization loop over a pointer-based
list:

.. literalinclude:: /examples/ug__init_access_list_zero/p.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__init_access_list_zero/p.adb
   :language: ada
   :linenos:

Like in the other variants, the postcondition of ``Init_List_Zero`` states that
the elements of the list ``L`` after the call are all ``0``. It uses the
``For_All_List`` function from ``Loop_Types`` to quantify over all the elements
of the list.
The loop iterates over the list ``L`` using a local borrower ``B`` which is
a local variable which borrows the ownership of a part of a datastructure for
the duration of its scope, see :ref:`Borrowing` for more details.
The loop invariant uses the ``At_End`` function to express properties about the
values of ``L`` and ``B`` at the end of the borrow. It states that the elements
of ``L`` at the end of the borrow will all be ``0`` if the elements of ``B`` at
the end of the borrow are all ``0``. This is provable because we know while
verifying the invariant that the already traversed elements were all set to
``0`` and that they can no longer be changed during the scope of ``B``. With
this loop invariant, |GNATprove| is able to prove the postcondition of
``Init_List_Zero``:

.. literalinclude:: /examples/ug__init_access_list_zero/test.out
   :language: none

Consider now a case where the value assigned to each element is not the
same. For example, in procedure ``Init_Arr_Index`` below, each element of array
``A`` is assigned the value of its index:

.. literalinclude:: /examples/ug__init_arr_index/init_arr_index.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have the value of their index. With this loop invariant, |GNATprove| is
able to prove the postcondition of ``Init_Arr_Index``, namely that all elements
of the array have the value of their index:

.. literalinclude:: /examples/ug__init_arr_index/test.out
   :language: none

As for ``Init_Arr_Zero`` above, it is possible to annotate ``A`` with the
Relaxed_Initialization aspect to use proof to verify its correct initialization:

.. literalinclude:: /examples/ug__init_arr_index_relaxed_init/init_arr_index.adb
   :language: ada
   :linenos:

Everything is proved by |GNATprove|:

.. literalinclude:: /examples/ug__init_arr_index_relaxed_init/test.out
   :language: none

Similarly, variants of ``Init_Vec_Zero`` and ``Init_List_Zero`` that assign a
different value to each element of the collection would be proved by
|GNATprove|.

.. index:: Loop_Invariant; mapping loops

Mapping Loops
^^^^^^^^^^^^^

This kind of loops iterates over a collection to map every element of the
collection to a new value:

 ================  ========================
 Loop Pattern      Separate Modification of Each Element
 ================  ========================
 Proof Objective   Every element of the collection has an updated value.
 Loop Behavior     Loops over the collection and updates every
                   element of the collection.
 Loop Invariant    Every element updated so far has its specific value.
 ================  ========================

In the simplest case, every element is assigned a new value based only on its
initial value. For example, in procedure ``Map_Arr_Incr`` below, every element
of array ``A`` is incremented by one:

.. literalinclude:: /examples/ug__map_arr_incr/map_arr_incr.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have been incremented (using :ref:`Attribute Loop_Entry`). With this loop
invariant, |GNATprove| is able to prove the postcondition of ``Map_Arr_Incr``,
namely that all elements of the array have been incremented:

.. literalinclude:: /examples/ug__map_arr_incr/test.out
   :language: none

Note that the commented loop invariant expressing that other elements have not
been modified is not needed, as it is an example of :ref:`Automatically
Generated Loop Invariants`.

Consider now a variant of the same initialization loop over a vector:

.. literalinclude:: /examples/ug__map_vec_incr/map_vec_incr.adb
   :language: ada
   :linenos:

Like before, we need an additionnal loop invariant to state that the length of
the vector is not modified by the loop. The other two invariants are direct
translations of those used for the loop over arrays: the first one expresses
that all elements up to the current loop index ``J`` have been incremented, and
the second one expresses that other elements have not been modified.
Note that, as formal vectors are limited, we need to use the ``Model`` function
of vectors to express the set of elements contained in the vector before the
loop (using attributes ``Loop_Entry`` and ``Old``).
With this loop invariant, |GNATprove| is able to prove the postcondition of
``Map_Vec_Incr``, namely that all elements of the vector have been incremented:

.. literalinclude:: /examples/ug__map_vec_incr/test.out
   :language: none

Similarly, consider a variant of the same mapping loop over a list:

.. literalinclude:: /examples/ug__map_list_incr/map_list_incr.adb
   :language: ada
   :linenos:

Like before, we need to use a cursor to iterate over the list. The loop
invariants express that all elements up to the current loop index ``J`` have
been incremented and that other elements have not been modified. Note that it is
necessary to state here that the length of the list is not modified during the
loop. It is because the length is used to bound the quantification over the
elements of the list both in the invariant and in the postcondition. With this
loop invariant, |GNATprove| is able to prove the postcondition of
``Map_List_Incr``, namely that all elements of the list have been incremented:

.. literalinclude:: /examples/ug__map_list_incr/test.out
   :language: none

Finally, consider a variant of the same mapping loop over a pointer-based
list:

.. literalinclude:: /examples/ug__map_access_list_incr/p.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__map_access_list_incr/p.adb
   :language: ada
   :linenos:

Like in the other variants, the precondition of ``Map_List_Incr`` states that
all elements of the input list ``L`` are less than ``Component_T'Last`` before
the call. It uses the ``For_All_List`` function from ``Loop_Types`` to
quantify over all the elements of the list. The postcondition is weaker than in
other variants of the loop. Indeed, referring to the value of a pointer-based
datastructure before the call is not allowed in the |SPARK| language.
Therefore we changed the postcondition to state instead that
all elements of the list are bigger than ``Component_T'First`` after the call.

The loop iterates over the list ``L`` using a local borrower ``B`` which is
a local variable which borrows the ownership of a part of a datastructure for
the duration of its scope, see :ref:`Borrowing` for more details.
The loop invariant is made of two parts. The first one states that the initial
property still holds on the elements of ``L`` accessible through ``B``. The
second uses the ``At_End`` function to express properties about the values
of ``L`` and ``B`` at the end of the borrow. It states that the elements of
``L`` at the end of the borrow will have the ``Bigger_Than_First`` property
if the elements of ``B`` at the end of the borrow have this property. This is
provable because we know when verifying the invariant that the already traversed
elements currently have the ``Bigger_Than_First`` property and that they can
no longer be changed during the scope of ``B``. With this
loop invariant, |GNATprove| is able to prove the postcondition of
``Map_List_Incr``:

.. literalinclude:: /examples/ug__map_access_list_incr/test.out
   :language: none

If we want to retain the most precise postcondition relating the elements of
the structure before and after the loop, we need to introduce a way to store
the values of the list before the call in a separate data structure. In the
following example, it is done by declaring a ``Copy`` function which returns
a copy of its input list. In its postcondition, we use the two-valued
``For_All_List`` function to state that the elements of the new structure
are equal to the elements of the input structure. An alternative could be
to store the elements in a structure not subject to ownership like an array.

.. note::

   The function ``Copy`` is marked as ``Import`` as it is not meant to be
   executed. It could be implemented in |SPARK| by returning a deep copy of the
   argument list, reallocating all cells of the list in the result.

.. literalinclude:: /examples/ug__map_access_list_incr_copy/p.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__map_access_list_incr_copy/p.adb
   :language: ada
   :linenos:

The postcondition of ``Map_List_Incr`` is similar to the postcondition of
``Copy``. It uses the two-valued ``For_All_List`` function to relate the
elements of ``L`` before and after the call. Like in the previous variant, the
loop traverses ``L`` using a local borrower ``B``. To be able to speak
about the initial value of ``L`` in the invariant, we introduce a ghost
constant ``L_Old`` storing a copy of this value. As we need to traverse both
lists at the same time, we declare a ghost variable ``B_Old`` as a local
observer of ``L_Old``.

The loop invariant is made of three parts now. The first one is similar to the
one in the previous example. The third loop invariant is a direct adaptation of
the second loop invariant of the previous example. It states that if, at the end
of the borrow, the values accessible through ``B`` are related to their
equivalent element in ``B_Old`` through ``Is_Incr``, then so are all the
elements of ``L``. The loop invariant in the middle states that the elements
reachable through ``B`` have not been modified by the loop. |GNATprove| can
verify these loop invariants as well as the postcondition of ``Map_List_Incr``:

.. literalinclude:: /examples/ug__map_access_list_incr_copy/test.out
   :language: none

.. note::

   The second loop invariant does not subsume the first. Indeed, proving that,
   if all elements of ``L_Old`` are small enough, so are all elements of an
   unknown observer ``B_Old`` of ``L_Old``, is beyond the capacity of
   |GNATprove|.

.. index:: Loop_Invariant; validation loops

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

.. literalinclude:: /examples/ug__validate_arr_zero/validate_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have value zero. With this loop invariant, |GNATprove| is able to prove
the postcondition of ``Validate_Arr_Zero``, namely that output parameter
``Success`` is True if-and-only-if all elements of the array have value zero:

.. literalinclude:: /examples/ug__validate_arr_zero/test.out
   :language: none

Consider now a variant of the same validation loop over a vector:

.. literalinclude:: /examples/ug__validate_vec_zero/validate_vec_zero.adb
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

.. literalinclude:: /examples/ug__validate_vec_zero/test.out
   :language: none

Similarly, consider a variant of the same validation loop over a list:

.. literalinclude:: /examples/ug__validate_list_zero/validate_list_zero.adb
   :language: ada
   :linenos:

Like in the case of ``Init_List_Zero`` seen previously, we need to define a
cursor here to iterate over the list. The loop invariant expresses that all
elements up to the current cursor ``Cu`` have the value zero. With this loop
invariant, |GNATprove| is able to prove the postcondition of
``Validate_List_Zero``, namely that output parameter ``Success`` is True
if-and-only-if all elements of the list have value zero:

.. literalinclude:: /examples/ug__validate_list_zero/test.out
   :language: none

The case of sets and maps is similar to the case of lists.

Consider now a variant of the same validation loop over a pointer-based list:

.. literalinclude:: /examples/ug__validate_access_list_zero/p.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__validate_access_list_zero/p.adb
   :language: ada
   :linenos:

The loop is implemented using a local observer (see :ref:`Observing`) which
borrows a read-only permission over a part of a datastructure until the end
of the scope of the observer. In the loop invariant, we cannot, like in
the other versions of the algorithm, speak about the value of the elements
which have already been traversed to say that they are all ``0``. Instead,
we state that the list ``L`` only contains ``0`` iff ``C`` only contains ``0``.
This is true since the loop exits as soon as a non-zero value is encountered.
With this invariant, the postcondition can be proved by |GNATprove|:

.. literalinclude:: /examples/ug__validate_access_list_zero/test.out
   :language: none

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

.. literalinclude:: /examples/ug__validate_full_arr_zero/validate_full_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant has been modified to state that all elements up to the
current loop index J have value zero if-and-only-if the output parameter
Success is True. This in turn requires to move the assignment of ``Success``
before the loop. With this loop invariant, |GNATprove| is able to prove the
postcondition of ``Validate_Full_Arr_Zero``, which is the same as the
postcondition of ``Validate_Arr_Zero``, namely that output parameter
``Success`` is True if-and-only-if all elements of the array have value zero:

.. literalinclude:: /examples/ug__validate_full_arr_zero/test.out
   :language: none

Similarly, variants of ``Validate_Vec_Zero`` and ``Validate_List_Zero`` that
keep validating elements of the collection after a non-zero element has been
encountered would be proved by |GNATprove|.

.. index:: Loop_Invariant; counting loops

Counting Loops
^^^^^^^^^^^^^^

This kind of loops iterates over a collection to count the number of elements
of the collection that satisfy a given criterion:

 ===============  ===================================================
 Loop Pattern      Count Elements Satisfying Criterion
 ===============  ===================================================
 Proof Objective   Count elements that satisfy a given criterion.
 Loop Behavior     Loops over the collection. Increments a counter each time
                   the value of an element satisfies the criterion.
 Loop Invariant    The value of the counter is either 0 when no element
                   encountered so far satisfies the criterion, or a positive
                   number bounded by the current iteration of the loop
                   otherwise.
 ===============  ===================================================

Consider a procedure ``Count_Arr_Zero`` that counts elements with value zero
in array ``A``:

.. literalinclude:: /examples/ug__count_arr_zero/count_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that the value of ``Counter`` is a natural number
bounded by the current loop index ``J``, and that ``Counter`` is equal to zero
exactly when all elements up to the current loop index have a non-zero value.
With this loop invariant, |GNATprove| is able to prove the postcondition of
``Count_Arr_Zero``, namely that output parameter ``Counter`` is a natural
number bounded by the length of the array ``A``, and that ``Counter`` is equal
to zero exactly when all elements in ``A`` have a non-zero value:

.. literalinclude:: /examples/ug__count_arr_zero/test.out
   :language: none

Consider now a variant of the same counting loop over a vector:

.. literalinclude:: /examples/ug__count_vec_zero/count_vec_zero.adb
   :language: ada
   :linenos:

Like before, the loop invariant expresses that the value of ``Counter`` is a
natural number bounded by the current loop index ``J``, and that ``Counter`` is
equal to zero exactly when all elements up to the current loop index have a
non-zero value.  With this loop invariant, |GNATprove| is able to prove the
postcondition of ``Count_Vec_Zero``, namely that output parameter ``Counter``
is a natural number bounded by the length of the vector ``V``, and that
``Counter`` is equal to zero exactly when all elements in ``V`` have a non-zero
value:

.. literalinclude:: /examples/ug__count_vec_zero/test.out
   :language: none

.. index:: Loop_Invariant; search loops

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

.. literalinclude:: /examples/ug__search_arr_zero/search_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have a non-zero value. With this loop invariant, |GNATprove| is able to
prove the postcondition of ``Search_Arr_Zero``, namely that output parameter
``Success`` is True if-and-only-if there is an element of the array that has
value zero, and that ``Pos`` is the index of such an element:

.. literalinclude:: /examples/ug__search_arr_zero/test.out
   :language: none

Consider now a variant of the same search loop over a vector:

.. literalinclude:: /examples/ug__search_vec_zero/search_vec_zero.adb
   :language: ada
   :linenos:

Like before, the loop invariant expresses that all elements up to the current
loop index ``J`` have a non-zero value. With this loop invariant, |GNATprove|
is able to prove the postcondition of ``Search_Vec_Zero``, namely that output
parameter ``Success`` is True if-and-only-if there is an element of the vector
that has value zero, and that ``Pos`` is the index of such an element:

.. literalinclude:: /examples/ug__search_vec_zero/test.out
   :language: none

Similarly, consider a variant of the same search loop over a list:

.. literalinclude:: /examples/ug__search_list_zero/search_list_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current cursor ``Cu``
have a non-zero value. With this loop invariant, |GNATprove| is able to prove
the postcondition of ``Search_List_Zero``, namely that output parameter
``Success`` is True if-and-only-if there is an element of the list that has
value zero, and that ``Pos`` is the cursor of such an element:

.. literalinclude:: /examples/ug__search_list_zero/test.out
   :language: none

The case of sets and maps is similar to the case of lists.

Consider a variant of the same search loop over a pointer-based list:

.. literalinclude:: /examples/ug__search_access_list_zero/p.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__search_access_list_zero/p.adb
   :language: ada
   :linenos:

As our pointer-based lists do not support cursors, the result of the search
is a pointer inside the list which can be used to access or even update the
corresponding element. Storing such an object inside an OUT parameter would
break the ownership model of SPARK by creating an alias. Instead, we use a
traversal function (see :ref:`Traversal Functions`) to return this pointer
as a local borrower of the input list. Since we now have a function, we can
no longer have an explicit ``Success`` flag to encode whether or not the value
was found. Instead, we simply return ``null`` in case of failure.

The loop iterates over the input list ``L`` using a local borrower ``B``. The
iteration stops when either ``B`` is ``null`` or ``B.Value`` is zero. In the
loop invariant, we cannot speak directly about the elements of ``L`` that have
been traversed to say that they are not ``0``. Instead, we write in the
invariant that ``L`` contains only non-zero values iff ``B`` contains only
non-zero values. Thanks to this loop invariant, |GNATprove| is able to verify
the postcondition of ``Search_List_Zero``:

.. literalinclude:: /examples/ug__search_access_list_zero/test.out
   :language: none

For more complex examples of search loops, see the :ref:`SPARK Tutorial` as
well as the section on :ref:`How to Write Loop Invariants`.

.. index:: Loop_Invariant; maximize loops

Maximize Loops
^^^^^^^^^^^^^^

This kind of loops iterates over a collection to search an element of the
collection that maximizes a given optimality criterion:

 ================  ========================
 Loop Pattern      Search Optimum to Criterion
 ================  ========================
 Proof Objective   Find an element or position that maximizes an optimality
                   criterion.
 Loop Behavior     Loops over the collection. Records maximum value of
                   criterion so far and possibly index that maximizes this criterion.
 Loop Invariant    Exactly one element encountered so far corresponds to
                   the recorded maximum over other elements encountered so far.
 ================  ========================

Consider a procedure ``Search_Arr_Max`` that searches an element maximum value
in array ``A``:

.. literalinclude:: /examples/ug__search_arr_max/search_arr_max.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have a value less than ``Max``, and that ``Max`` is the value of one of
these elements. The last loop invariant gives in fact this element, it is
``A(Pos)``, but this part of the loop invariant may not be present if the
position ``Pos`` for the optimum is not recorded. With this loop invariant,
|GNATprove| is able to prove the postcondition of ``Search_Arr_Max``, namely
that output parameter ``Max`` is the maximum of the elements in the array, and
that ``Pos`` is the index of such an element:

.. literalinclude:: /examples/ug__search_arr_max/test.out
   :language: none

Consider now a variant of the same search loop over a vector:

.. literalinclude:: /examples/ug__search_vec_max/search_vec_max.adb
   :language: ada
   :linenos:

Like before, the loop invariant expresses that all elements up to the current
loop index ``J`` have a value less than ``Max``, and that ``Max`` is the value
of one of these elements, most precisely the value of ``Element (V, Pos)`` if
the position ``Pos`` for the optimum is recorded. An additional loop invariant
is needed here compared to the case of arrays to state that ``Pos`` remains
within the bounds of the vector. With this loop invariant, |GNATprove| is able
to prove the postcondition of ``Search_Vec_Max``, namely that output parameter
``Max`` is the maximum of the elements in the vector, and that ``Pos`` is the
index of such an element:

.. literalinclude:: /examples/ug__search_vec_max/test.out
   :language: none

Similarly, consider a variant of the same search loop over a list:

.. literalinclude:: /examples/ug__search_list_max/search_list_max.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current cursor ``Cu``
have a value less than ``Max``, and that ``Max`` is the value of one of these
elements, most precisely the value of ``Element (L, Pos)`` if the cursor
``Pos`` for the optimum is recorded.  Like for vectors, an additional loop
invariant is needed here compared to the case of arrays to state that cursor
``Pos`` is a valid cursor of the list. A minor difference is that a loop
invariant now starts with ``Max = 0 or else ..`` because the loop invariant is
stated at the start of the loop (for convenience with the use of
``First_To_Previous``) which requires this modification. With this loop
invariant, |GNATprove| is able to prove the postcondition of
``Search_List_Max``, namely that output parameter ``Max`` is the maximum of the
elements in the list, and that ``Pos`` is the cursor of such an element:

.. literalinclude:: /examples/ug__search_list_max/test.out
   :language: none

The case of sets and maps is similar to the case of lists.

Consider a variant of the same search loop over a pointer-based list:

.. literalinclude:: /examples/ug__search_access_list_max/p.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__search_access_list_max/p.adb
   :language: ada
   :linenos:

As our pointer-based lists do not support cursors, the result of the search
is a pointer inside the list which can be used to access or even update the
corresponding element. Storing such an object inside an OUT parameter would
break the ownership model of SPARK by creating an alias. Instead, we use a
traversal function (see :ref:`Traversal Functions`) to return this pointer
as a local borrower of the input list. Since we now have a function, we can
no longer explicitely return the value of the maximum. It is not a problem,
as it can be accessed easily as the ``Value`` component of the returned
pointer. In the postcondition of ``Search_List_Max``, we cannot use
``For_All_List`` to express that the returned pointer designates the maximum
value in the list. Indeed, the property depends on the value of this maximum.
Instead, we create a specific recursive function taking the maximum as an
additional parameter.

The iteration over the input list ``L`` uses a local borrower ``B``. It is
expressed as two nested loops. The inner loop declares a local borrower ``Prec``
to register the current value of the maximum. Then it iterates through the loop
using ``B`` until a value bigger than the current maximum is found. The outer
loop repeats this step as many times as necessary. This split into two loops
is necessary as the |SPARK| language prevents borrowers from jumping into a
different part of the data structure. As ``B`` is not syntactically a path
rooted at ``Prec``, ``Prec`` cannot be assigned the current value of ``B`` when
a new maximal value is found. We therefore need to create a new variable
to hold the current maximum each time it changes.

In the loop invariant of the outer loop, we cannot speak directly about the
elements of ``L`` that have been traversed to say that they are smaller than
the current maximum. Instead, we write in the invariant that the all values of
``L`` are smaller than any given value bigger than the current maximum iff the
values of ``B`` are. A similar invariant is necessary on the inner loop.
Thanks to these loop invariants, |GNATprove| is able to verify
the postcondition of ``Search_List_Max``:

.. literalinclude:: /examples/ug__search_access_list_max/test.out
   :language: none

The loop variants state that the length of ``B`` is strictly
decreasing. This is used to prove that the loop terminates.

For more complex
examples of search loops, see the :ref:`SPARK Tutorial` as well as the section
on :ref:`How to Write Loop Invariants`.

.. index:: Loop_Invariant; update loops

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

.. literalinclude:: /examples/ug__update_arr_zero/update_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current loop index
``J`` have been zeroed out if initially smaller than ``Threshold`` (using
:ref:`Attribute Loop_Entry`). With this loop invariant, |GNATprove| is able to
prove the postcondition of ``Update_Arr_Zero``, namely that all elements
initially smaller than ``Threshold`` have been zeroed out, and that other
elements have not been modified:

.. literalinclude:: /examples/ug__update_arr_zero/test.out
   :language: none

Note that the commented loop invariant expressing that other elements have not
been modified is not needed, as it is an example of :ref:`Automatically
Generated Loop Invariants`.

Consider now a variant of the same update loop over a vector:

.. literalinclude:: /examples/ug__update_vec_zero/update_vec_zero.adb
   :language: ada
   :linenos:

Like for ``Map_Vec_Incr``, we need to use the ``Model`` function over arrays to
access elements of the vector before the loop as the vector type is limited. The
loop invariant expresses that all elements up to the current loop index ``J``
have been zeroed out if initially smaller than ``Threshold``, that elements that
follow the current loop index have not been modified, and that the length of
``V`` is not modified (like in ``Init_Vec_Zero``). With this loop invariant,
|GNATprove| is able to prove the postcondition of ``Update_Vec_Zero``:

.. literalinclude:: /examples/ug__update_vec_zero/test.out
   :language: none

Similarly, consider a variant of the same update loop over a list:

.. literalinclude:: /examples/ug__update_list_zero/update_list_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements up to the current cursor ``Cu``
have been zeroed out if initially smaller than ``Threshold`` (using function
``Model`` to access the element stored at a given position in the list and
function ``Positions`` to query the position of the current cursor), and that
elements that follow the current loop index have not been
modified. Note that it is
necessary to state here that the length of the list is not modified during the
loop. It is because the length is used to bound the quantification over the
elements of the list both in the invariant and in the postcondition.

With this loop invariant, |GNATprove| is able to prove the postcondition of
``Update_List_Zero``, namely that all elements initially smaller than
``Threshold`` have been zeroed out, and that other elements have not been
modified:

.. literalinclude:: /examples/ug__update_list_zero/test.out
                    :language: none

The case of sets and maps is similar to the case of lists.

Consider now a variant of the same update loop over a pointer-based list.
To express the postcondition relating the elements of the structure before and
after the loop, we need to introduce a way to store the values of the list
before the call in a separate data structure. Indeed, the ``Old`` attribute
cannot be used on ``L`` directly has it would introduce an alias. In this
example, it is done by declaring a ``Copy`` function which returns
a copy of its input list. In its postcondition, we use the two-valued
``For_All_List`` function to state that the elements of the new structure
are equal to the elements of its input structure. An alternative could be
to store the elements in a structure not subject to ownership like an array.

.. note::

   The function ``Copy`` is marked as ``Import`` as it is not meant to be
   executed. It could be implemented in |SPARK| by returning a deep copy of the
   argument list, reallocating all cells of the list in the result.

.. literalinclude:: /examples/ug__update_access_list_zero/p.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__update_access_list_zero/p.adb
   :language: ada
   :linenos:

In the postcondition of ``Update_List_Zero``, we cannot use ``For_All_List`` to
express the relation between the values of the list before and after the call.
Indeed, the relation depends on the value of the input ``Threshold``.
Instead, we create a specific recursive function taking the threshold as an
additional parameter.

The loop traverses ``L`` using a local borrower ``B``. To be able to speak
about the initial value of ``L`` in the invariant, we introduce a ghost
constant ``L_Old`` storing a copy of this value. As we need to traverse both
lists at the same time, we declare a ghost variable ``B_Old`` as a local
observer of ``L_Old``.

The loop invariant is made of two parts. The first one states that the elements
reachable through ``B`` have not been modified by the loop. In the second loop
invariant, we want to use ``Updated_If_Less_Than_Threshold`` to relate the
elements of ``L`` that were already traversed to the elements of ``L_Old``.
As we cannot speak specifically about the traversed elements of ``L``, the
invariant states that, if at the end of the borrow the values accessible
through ``B`` are related to their equivalent element in ``B_Old`` through
``Updated_If_Less_Than_Threshold``, then so are all the elements of ``L``.
|GNATprove| can verify these invariants as well as the postcondition of
``Update_List_Zero``:

.. literalinclude:: /examples/ug__update_access_list_zero/test.out
   :language: none

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

.. literalinclude:: /examples/ug__update_range_arr_zero/update_range_arr_zero.adb
   :language: ada
   :linenos:

The loop invariant expresses that all elements between ``First`` and the
current loop index ``J`` have been zeroed out, and that other elements have not
been modified (using a combination of :ref:`Attribute Loop_Entry` and
:ref:`Delta Aggregates` to express this concisely). With this loop invariant,
|GNATprove| is able to prove the postcondition of ``Update_Range_Arr_Zero``,
namely that all elements between ``First`` and ``Last`` have been zeroed out,
and that other elements have not been modified:

.. literalinclude:: /examples/ug__update_range_arr_zero/test.out
   :language: none

Consider now a variant of the same update loop over a vector:

.. literalinclude:: /examples/ug__update_range_vec_zero/update_range_vec_zero.adb
   :language: ada
   :linenos:

Like for ``Map_Vec_Incr``, we need to use the ``Model`` function over arrays to
access elements of the vector before the loop as the vector type is limited. The
loop invariant expresses that all elements between ``First`` and current loop
index ``J`` have been zeroed, and that other elements have not been modified.
With this loop invariant, |GNATprove| is able to prove the
postcondition of ``Update_Range_Vec_Zero``:

.. literalinclude:: /examples/ug__update_range_vec_zero/test.out
   :language: none

Similarly, consider a variant of the same update loop over a list:

.. literalinclude:: /examples/ug__update_range_list_zero/update_range_list_zero.adb
   :language: ada
   :linenos:

Compared to the vector example, it requires three additional invariants. As the
loop is done via a cursor, the first two loop invariants are necessary to know
that the current cursor ``Cu`` stays between ``First`` and ``Last`` in the list.
The fourth loop invariant states that the position of cursors in ``L`` is not
modified during the loop. It is necessary to know that the two cursors ``First`` and
``Last`` keep designating the same range after the loop. With this loop invariant,
|GNATprove| is able to prove the postcondition of ``Update_Range_List_Zero``,
namely that all elements between ``First`` and ``Last`` have been zeroed out,
and that other elements have not been modified:

.. literalinclude:: /examples/ug__update_range_list_zero/test.out
   :language: none
