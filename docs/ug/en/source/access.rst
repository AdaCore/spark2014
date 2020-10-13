Pointer Support and Dynamic Memory Management
=============================================

.. index:: ownership; analysis of
           access types; access to object

Access to Objects and Ownership
-------------------------------

In |SPARK|, values of an access-to-object type are subjected to a
:ref:`Memory Ownership Policy`. The idea is that an object designated by a
pointer always has a single owner, which retains the right to either modify it,
or (exclusive or) share it with others in a read-only way. Said otherwise, we
always have either several copies of the pointer that allow only reading, or
only a single copy of the pointer that allows modification.

The main idea used to enforce single ownership for pointers is the move
semantics of assignments. When a pointer is copied through an assignment
statement, the ownership of the pointer is transferred to the left hand side of
the assignment. As a result, the right hand side loses the ownership of the
object, and therefore loses the right to access it, both for writing and
reading. In the example below, the assignment from ``X`` to ``Y`` causes ``X``
to lose ownership on the value it references:

.. literalinclude:: /examples/tests/access1/test.adb
   :language: ada
   :linenos:

As a result, the last assertion, which reads the value of ``X``, is illegal in
|SPARK|, leading to an error message from |GNATprove|:

.. literalinclude:: /examples/tests/access1/test.out
   :language: none
   :linenos:

In this example, we can see the point of these ownership rules. To correctly
reason about the semantics of a program, |SPARK| needs to know, when a change is
made, what are the objects that are potentially impacted. Because it assumes
that there can be no aliasing (at least no aliasing of mutable data,
see :ref:`Absence of Interferences`), the tool
can easily determine what are the parts of the environment that are updated
by a statement, be it a simple assignment, or for example a procedure call. If
we were to break this assumption, we would need to either assume the worst
(that all references can be aliases of each other) or require the user to
explicitly annotate subprograms to describe which references can be aliased and
which cannot. In our example, |SPARK| can deduce that an assignment to ``Y``
cannot impact ``X``. This is only correct because of ownership rules that
prevent us from accessing the value of ``X`` after the update of ``Y``.

Note that a variable which has been moved is not necessarily lost for the rest
of the program. Indeed, it is possible to assign it again, restoring ownership.
For example, here is a piece of code that swaps the pointers ``X`` and ``Y``:

.. literalinclude:: /examples/tests/access2/test.adb
   :language: ada
   :linenos:

This code is accepted by |GNATprove|. Intuitively, we can see that writing
at top-level into ``X`` after it has been moved is OK, since it will not modify
the actual owner of the moved value (here ``Tmp``). However, writing in
``X.all`` is forbidden, as it would affect ``Tmp``:

.. literalinclude:: /examples/tests/access3/test.adb
   :language: ada
   :linenos:

The above variant is rejected by |GNATprove|:

.. literalinclude:: /examples/tests/access3/test.out
   :language: none
   :linenos:

.. index:: deallocation
           Unchecked_Deallocation
           access types; deallocation

Deallocation
------------

At the end of its lifetime, unless the memory it points to is transferred to
another owner, an owning pointer should be deallocated. This is typically
achieved by instantiating the standard generic procedure
``Ada.Unchecked_Deallocation`` with the type of the underlying ``Object`` and
the type ``Name`` of the access type:

.. literalinclude:: /examples/tests/access4/test.adb
   :language: ada
   :linenos:

|GNATprove| guarantees the absence of memory leak in the above code:

.. literalinclude:: /examples/tests/access4/test.out
   :language: none
   :linenos:

Notice that there are three kinds of checks for memory leaks:

1. On each assignment, |GNATprove| checks that the left-hand side is not
   leaking memory. That's the case on the assignment to ``Y`` above on line 11.

2. On each declaration, |GNATprove| checks that the object is not leaking
   memory at the end of its lifetime. That's the case for the declarations of
   ``X`` and ``Y`` above on lines 8 and 9.

3. On each call to an instance of ``Ada.Unchecked_Deallocation``, |GNATprove|
   checks that the underlying memory is not itself owning memory. Above, the
   object pointed to is an integer, so this holds trivially.

Here is an example of code with all three cases of memory leaks:

.. literalinclude:: /examples/tests/access5/test.adb
   :language: ada
   :linenos:

|GNATprove| detects all three memory leaks in the above code:

.. literalinclude:: /examples/tests/access5/test.out
   :language: none
   :linenos:

Finally, in a case like above where a data structure manipulated through
pointers also contains pointers, it is customary to define deallocation
procedures to take care of deallocating the complete subtree of allocated
memory. This is done in the following code by defining a higher-level ``Free``
procedure applying to arguments of type ``Int_Ptr_Ptr``, which is based on
instances of ``Ada.Unchecked_Deallocation`` for deallocating individual memory
chunks:

.. literalinclude:: /examples/tests/access6/test.adb
   :language: ada
   :linenos:

Note the contract of the higher-level ``Free`` procedure, with a postcondition
stating that ``X`` is null on exit, and correct dependences taking into account
the internal abstract state ``SPARK.Heap.Dynamic_Memory`` representing the
state of the standard dynamic allocator (as presented in :ref:`SPARK Heap
Library`), similar to what is defined for the standard
``Ada.Unchecked_Deallocation`` procedure in SPARK RM 3.10. |GNATprove|
guarantees that the above code is correctly deallocating memory:

.. literalinclude:: /examples/tests/access6/test.out
   :language: none
   :linenos:

Observing
---------

The ownership policy of |SPARK| allows sharing a single reference between
several readers. This mechanism is called `observing`. When a variable is
observed, both the observed object and the observer retain the right to read
the object, but none can modify it. When the observer disappears, the observed
object regains the permissions it had before (read-write or read-only).

To declare an observer, it is necessary to use an anonymous access-to-constant
type. It is what allows the tool to tell the difference between moving and
observing a value. Here is
an example. We have a list ``L``, defined as a recursive pointer-based data
structure in the usual way.  We then observe its tail by introducing a local
observer ``N`` using an anonymous access to constant type. We then do it again
to observe the tail of ``N``:

.. code-block:: ada

   type List;
   type List_Acc is access List;
   type List is record
      Value : Element;
      Next  : List_Acc;
   end record;

   L : List := ...;

   declare
      N : access constant List := L.Next; -- observe part of L
   begin
      declare
         M : access constant List := N.Next; -- observe again part of N
      begin
         pragma Assert (M.Value = 3); --  M can be read
         pragma Assert (N.Value = 2); --  but we can still read N
         pragma Assert (L.Value = 1); --  and even L
      end;
   end;
   L.Next := null; --  all observers are out of scope, we can modify L

We can see that the three variables retain the right to read their content. But
it is OK as none of them is allowed to update it. When no more observers exist,
it is again possible to modify ``L``.

It is not possible to update a data structure through an observer, but it does
not mean that the observer itself is necessarily a constant.
It is possible to update it so that it designates
another part of a data structure. This is especially useful to traverse
recursive data structures using loops. As an example, here is a function which
searches for the an element ``E`` in a list ``L``:

.. code-block:: ada

   function Contains (L : access constant List; E : Element) return Boolean is
      C : access constant List := L; --  C observes L
   begin
      while C /= null loop
         if C.Value = E then
            return True;
         end if;
         C := C.Next; --  C now designates the tail of the list
      end loop;
      return False;
   end Contains;

A local observer ``C`` is used to traverse the list ``L``. At each iteration of
the loop, ``C`` is shifted so that it designates one element further in the
list.

Borrowing
---------

Moving is not the only way to transfer ownership. It is also possible to
`borrow` the ownership of (a part of) an object for a period of time. During
this period, the part of the object which was borrowed can only be accessed
through the borrower. When the borrower disappears (goes out of scope), the
borrowed object regains the ownership, and is
accessible again. It is what happens for example for mutable parameters of a
subprogram when the subprogram is called. The ownership of the actual parameter
is transferred to the formal parameter for the duration of the call, and should
be returned when the subprogram terminates. In particular, this disallows
procedures that move some of their parameters away, as in the following example:

.. code-block:: ada
   :linenos:

   type Int_Ptr_Holder is record
      Content : Int_Ptr;
   end record;

   procedure Move (X : in out Int_Ptr_Holder; Y : in out Int_Ptr_Holder) is
   begin
      X := Y; --  ownership of Y.Content is moved to X.Content
   end Move;

.. code-block:: none

   insufficient permission for "Y" when returning from "Move"
   object was moved at line 7

Note that borrowing does not occur on subprogram calls for in out parameters
of a named access type. Indeed, |SPARK| RM has a special wording for these
parameters, stating that they are not borrowed but moved on entry and on exit
of the subprogram. This allows us to move these parameters inside the call, so
they can designate something else (or be set to ``null``), which otherwise
would be forbidden, as borrowed top-level access objects cannot be moved
(but parts of such objects can be moved).

The ownership policy of |SPARK| also allows declaring local borrowers in a
nested scope by using an anonymous access-to-variable type (without the
``constant`` keyword used above for an observer):

.. code-block:: ada

   declare
     Y : access Integer := X;    --  Y borrows the ownership of X
                                 --  for the duration of the declare block
   begin
     pragma Assert (Y.all = 10); --  Y can be accessed
     Y.all := 11;                --  both for reading and writing
   end;
   pragma Assert (X.all = 11);   --  The ownership of X is restored,
                                 --  it can be accessed again

Just like local observers, local borrowers are especially useful to modify a
recursive data structure through a loop. In the example below,
the procedure ``Replace_Element`` uses a loop to assign a new value ``E`` to
the element at position ``N`` in a list ``L``.

.. code-block:: ada

   procedure Replace_Element (L : access List; N : Positive; E : Element) is
      X : access List := L; --  X borrows the ownership of L
      P : Positive := N;
   begin
      while X /= null loop
         if P = 1 then
            X.Value := E; --  We use X to modify L arbitrarily deeply
            return;
         end if;
         X := X.Next; --  X now designates the tail of the list
         P := P - 1;
      end loop;
   end Replace_Element;

A local borrower ``X`` is used
to traverse the list and modify it in place. The two assignments to ``X`` in
the loop are different in essence. The first one assigns a part of the structure
designated by ``X``. It is a modification of the borrowed list ``L``. The
second one assigns ``X`` at top-level. It does not modify ``L``, but changes
``X`` so that it designates another the part of L. It is called a `reborrow`.
In |SPARK|, reborrows are only allowed to borrow a part of the borrower. Said
otherwise, a borrower can only go deeper in the data structure, it is not
allowed to jump to a distinct object or distinct part of the same
standalone object.

Borrowers essentially are statically known aliases of their borrowed objects.
As a consequence, verifying programs involving borrowers sometimes requires
describing the relation between the borrowed object and the borrower. This can
be done by :ref:`Supplying a Pledge for a Borrower`.

.. index:: traversal function

Traversal Functions
-------------------

It is possible to write a function which computes and returns an observer or a
borrower of an input data structure, provided the traversed data structure is
itself an access type. This is called a `traversal function`.

An `observing` traversal function takes an access type as its first parameter
and returns an anonymous access-to-constant object which should be a part of
this first parameter. As an example, we can write a function which returns a
value stored in a list as an anonymous access-to-constant type. To be able to
do this, we need to store an access to the value instead of the value itself in
the list:

.. code-block:: ada

   type List;
   type List_Acc is access List;
   type Element_Acc is not null access Element;
   type List is record
      Value : Element_Acc;
      Next  : List_Acc;
   end record;

   function Constant_Access (L : access constant List; N : Positive) return access constant Element
   is
      C : access constant List := L;
      P : Positive := N;
   begin
      while C /= null loop
         if P = 1 then
            return C.Value;
         end if;
         C := C.Next;
         P := P - 1;
      end loop;
      return null;
   end Constant_Access;

The function ``Constant_Access`` returns an access designating a value which is
already contained in the list ``L``. As per the ownership policy of |SPARK|, if
``Constant_Access`` was returning a named access type, it would be rejected.
However, since it returns an anonymous access-to-constant type, the return
statement is considered to create an observer of ``L``. Note that an observing
traversal function should necessarily observe its first parameter.

.. code-block:: ada

   declare
     C : access constant Element := Constant_Access (L, 3);
     --  C is an observer of L
   begin
     pragma Assert (C.all = L.Next.Next.Value.all);
     --  It is OK to read both C and L, but L cannot be modified
   end;
   L := null; --  L can be modified again

It is also possible to return a mutable access inside a data structure using a
`borrowing` traversal function. Just like observing traversal functions,
their borrowing counterparts take as a first parameter an access type, but they
have as a return type an anonymous access-to-variable type. The function
``Reference`` below is similar to ``Constant_Access`` except that both its
parameter and its return type are mutable:

.. code-block:: ada

   function Reference (L : access List; N : Positive) return access Element
   is
      C : access List := L;
      P : Positive := N;
   begin
      while C /= null loop
         if P = 1 then
            return C.Value;
         end if;
         C := C.Next;
         P := P - 1;
      end loop;
      return null;
   end Reference;

A borrowing traversal function returns a borrower of its first parameter. The
result of a call to ``Reference`` can be used to modify its actual parameter
arbitrarily deeply. Like for any borrowers, it is illegal to either read or
modify the parameter while the object storing the result of the call is still
in scope.

Note that it is possible to use pledges to describe the relation between the
result of a borrowing traversal function and its parameter in a postcondition,
see :ref:`Supplying a Pledge for a Borrower`.

.. index:: access types; access to subprogram

Supprogram Pointers
-------------------

Unlike access to objects, access to subprograms are not subjected to the
ownership policy of |SPARK|. Both anonymous and named access-to-subprogram
types are supported. As an example, the procedure ``Update_All`` below calls
its parameter ``Update_One`` on all the elements of its array parameter ``A``:

.. code-block:: ada

   procedure Update_All
     (A          : in out Nat_Array;
      Update_One : not null access procedure (X : in out Natural))
   is
   begin
      for E of A loop
         Update_One (E);
      end loop;
   end Update_All;

It can be called on any procedure with the correct profile:

.. code-block:: ada

   procedure Update_One (X : in out Natural);

   procedure Test (A : in out Nat_Array)  is
   begin
      Update_All (A, Update_One'Access);
   end Test;

As |GNATprove| verifies subprograms modularly, no precondition checks are
generated during the analysis of ``Update_All``. As a consequence, a check needs
to be performed in ``Test`` to make sure that the parameter supplied for
``Update_One`` does not have a precondition. For example, if we modify
``Update_One`` to have a precondition:

.. code-block:: ada

   function In_Range (X : Natural) return Boolean;

   procedure Update_One (X : in out Natural) with
     Pre  => In_Range (X);

Then |GNATprove| will complain on the call to ``Update_All`` that the
precondition of ``Update_One`` might not be satisfied:

.. code-block:: none

  medium: precondition of target might not be strong enough to imply precondition of source, cannot prove In_Range (X)

For postconditions, it is the opposite. No postconditions will be assumed when
verifying ``Update_All``, so it is perfectly OK if ``Update_One`` has any
postconditions. However, it will not be possible to use this postcondition to
prove anything on the effect of ``Update_All``.

.. index:: precondition; for subprogram pointer
           postcondition; for subprogram pointer

Contracts for Supprogram Pointers
---------------------------------

[Ada202X]

The upcoming standard of Ada allows adding contracts to access-to-subprogram
types. As an example, here is a named access type ``Update_Proc`` with a
contract:

.. code-block:: ada

   type Update_Proc is not null access procedure (X : in out Natural) with
     Pre  => In_Range (X),
     Post => Relation (X'Old, X);

The Ada standard mandates that, when a subprogram designated by an access type
with a contract is called, the contract is verified. Thus, it is possible
for |GNATprove| to use this contract on indirect calls. For example, we can use
``Update_Proc`` as the type of the ``Update_One`` parameter of ``Update_All``.
As the call to ``Update_One`` now has a precondition, we should ensure before a
call to ``Update_All`` that ``In_Range`` holds for all elements of ``A``. We
can also prove that ``Relation`` holds at every index of the array after the
call:

.. code-block:: ada

   procedure Update_All
     (A          : in out Nat_Array;
      Update_One : Update_Proc)
   with Pre  => (for all E of A => In_Range (E)),
        Post => (for all I in A'Range => Relation (A'Old (I), A (I)))
   is
   begin
      for K in A'Range loop
         Update_One (A (K));
         pragma Loop_Invariant
           (for all I in A'First .. K => Relation (A'Loop_Entry (I), A (I)));
      end loop;
   end Update_All;

As the contract of an access type is the only one which is known by |GNATprove|
when checking indirect callers, |SPARK| requires that this contract is a valid
approximation of the contract of every subprogram designated by an access
objects of this type. More precisely, each time a value of a given
access-to-subprogram type is created, |GNATprove| makes sur that:

* the precondition of the access-to-subprogram type if any (or the default
  precondition of True otherwise) is strong enough to imply the precondition of
  the designated subprogram, and
* the postcondition of the designated subprogram if any (or the default
  postcondition of True otherwise) is strong enough to imply the postcondition
  of the subprogram type.

Consider the three procedures below:

.. code-block:: ada

   procedure Update_One_1 (X : in out Natural) with
     Pre  => In_Range (X),
     Post => Relation (X'Old, X);
   --  Update_One_1 has exactly the same contract as Update_Proc

   procedure Update_One_2 (X : in out Natural) with
     Post => Relation (X'Old, X) and Relation_2 (X'Old, X);
   --  Update_Proc safely approximates Update_One_2:
   --    * the precondition of Update_Proc is enough to ensure that Update_One_2 can execute safely
   --    * the postcondition of Update_One_2 implies the postcondition of Update_Proc

   procedure Update_One_3 (X : in out Natural) with
     Pre  => In_Range (X);
   --  Does Relation hold after a call to Update_One_3?

   procedure Update_One_4 (X : in out Natural) with
     Pre  => In_Range (X) and In_Range_2 (X),
     Post => Relation (X'Old, X);
   --  Is it safe to call Update_One_4 when we do not check In_Range_2?

The procedures ``Update_One_1`` and ``Update_One_2``
can be designated by objects of type ``Update_Proc``, as their contract can be
safely approximated by the contract of ``Update_Proc``. The procedures
``Update_One_3`` and ``Update_One_4`` on the other hand cannot.
For example, if we try to use ``Update_One_3`` as a parameter of ``Update_All``,
|GNATprove| emits a check message stating that the postcondition of
``Update_Proc`` might not be valid after a call to ``Update_One_3``:

.. code-block:: ada

   procedure Test (A : in out Nat_Array) with
     Pre => (for all E of A => In_Range (E))
   is
   begin
      Update_All (A, Update_One_3'Access);
   end Test;

.. code-block:: none

  medium: postcondition of source might not be strong enough to imply postcondition of target, cannot prove Relation (X'Old, X)

Theoretically, a similar notion of approximation should be used for
:ref:`Data Dependencies` and :ref:`Flow Dependencies` contracts. However, as
these contracts are not currently allowed on access-to-subprogram types,
|SPARK| simply disallows taking the Access attribute on a suprogram which has
global inputs or outputs.
