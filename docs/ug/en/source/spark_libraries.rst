.. _SPARK Libraries:

|SPARK| Libraries
=================

.. _Functional Containers Library:

Functional Containers Library
-----------------------------

To model complex data structures, one often needs simpler, mathematical like
containers. The mathematical containers provided in the |SPARK| library are
unbounded and may contain indefinite elements. Furthermore, to be usable in
every context, they are neither controlled nor limited. So that these containers
can be used safely, we have made them functional, that is, no primitives are
provided which would allow modifying an existing container. Instead, their API
features functions creating new containers from existing ones. As an example,
functional containers provide no ``Insert`` procedure but rather a function
``Add`` which creates a new container with one more element than its parameter:

.. code-block:: ada

    function Add (C : Container; E : Element_Type) return Container;

As a consequence, these containers are highly inefficient. They are also memory
consuming as the allocated memory is not reclaimed when the container is no
longer referenced. Thus, they should in general be used in ghost code and
annotations so that they can be removed from the final executable.

There are 3 functional containers, which are part of the |GNAT Pro| standard
library:

* ``Ada.Containers.Functional_Maps``
* ``Ada.Containers.Functional_Sets``
* ``Ada.Containers.Functional_Vectors``

Sequences defined in ``Functional_Vectors`` are no more than ordered collections
of elements. In an Ada like manner, the user can choose the range used to index
the elements:


.. code-block:: ada

    function Length (S : Sequence) return Count_Type;
    function Get (S : Sequence; N : Index_Type) return Element_Type;

Functional sets offer standard mathematical set functionalities such as
inclusion, union, and intersection. They are neither ordered nor hashed:


.. code-block:: ada

    function Contains (S : Set; E : Element_Type) return Boolean;
    function "<=" (Left : Set; Right : Set) return Boolean;

Functional maps offer a dictionary between any two types of elements:


.. code-block:: ada

    function Has_Key (M : Map; K : Key_Type) return Boolean;
    function Get (M : Map; K : Key_Type) return Element_Type;

Each functional container type supports iteration as appropriate, so that its
elements can easily be quantified over.

These containers can easily be used to model user defined data structures. They
were used to this end to annotate and verify a package of allocators (see
`allocators` example in the :ref:`Examples in the Toolset Distribution`). In
this example, an allocator featuring a free list implemented in an array is
modeled by a record containing a set of allocated resources and a sequence of
available resources:

.. code-block:: ada

    type Status is (Available, Allocated);
    type Cell is record
       Stat : Status;
       Next : Resource;
    end record;
    type Allocator is array (Valid_Resource) of Cell;
    type Model is record
       Available : Sequence;
       Allocated : Set;
    end record;

.. note::

    Functional sets and maps represent elements modulo equivalence. For proof,
    the range of quantification over their content includes all elements that
    are equivalent to elements included in the container. On the other hand, for
    execution, the iteration is only done on elements which have actually been
    included in the container. This difference may make interaction between test
    and proof tricky when the equivalence relation is not the equality.

.. _Formal Containers Library:

Formal Containers Library
-------------------------

Containers are generic data structures offering a high-level view of
collections of objects, while guaranteeing fast access to their content to
retrieve or modify it. The most common containers are lists, vectors, sets and
maps, which are defined as generic units in the Ada Standard Library. In
critical software where verification objectives severely restrict the use of
pointers, containers offer an attractive alternative to pointer-intensive data
structures.

The Ada Standard Library defines two kinds of containers:

* The controlled containers using dynamic allocation, for example
  ``Ada.Containers.Vectors``. They define containers as controlled tagged
  types, so that memory for the container is automatic reallocated during
  assignment and automatically freed when the container object's scope ends.
* The bounded containers not using dynamic allocation, for example
  ``Ada.Containers.Bounded_Vectors``. They define containers as discriminated
  tagged types, so that the memory for the container can be reserved at
  initialization.

Although bounded containers are better suited to critical software development,
neither controlled containers nor bounded containers can be used in |SPARK|,
because their API does not lend itself to adding suitable contracts (in
particular preconditions) ensuring correct usage in client code.

The formal containers are a variation of the bounded containers with API
changes that allow adding suitable contracts, so that |GNATprove| can prove
that client code manipulates containers correctly. There are 7 formal
containers, which are part of the |GNAT Pro| standard library:

* ``Ada.Containers.Formal_Vectors``
* ``Ada.Containers.Formal_Indefinite_Vectors``
* ``Ada.Containers.Formal_Doubly_Linked_Lists``
* ``Ada.Containers.Formal_Hashed_Sets``
* ``Ada.Containers.Formal_Ordered_Sets``
* ``Ada.Containers.Formal_Hashed_Maps``
* ``Ada.Containers.Formal_Ordered_Maps``

Lists, sets and maps can only be used with definite objects (objects for which
the compiler can compute the size in memory, hence not ``String`` nor
``T'Class``). Vectors come in two flavors for definite objects
(``Formal_Vectors``) and indefinite objects (``Formal_Indefinite_Vectors``).

Lists, sets, maps, and definite vectors are always bounded. Indefinite vectors
can be bounded or unbounded
depending on the value of the formal parameter ``Bounded`` when instantiating
the generic unit. Bounded containers do not use dynamic allocation. Unbounded
vectors use dynamic allocation to expand their internal block of memory.

Modified API of Formal Containers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The visible specification of formal containers is in |SPARK|, with suitable
contracts on subprograms to ensure correct usage, while their private part
and implementation is not in |SPARK|. Hence, |GNATprove| can be used to prove
correct usage of formal containers in client code, but not to prove that formal
containers implement their specification.

Procedures ``Update_Element`` or ``Query_Element`` that iterate over a
container are not defined on formal containers. Specification and analysis of
such procedures that take an access-to-procedure in parameter is beyond the
capabilities of |SPARK| and |GNATprove|. See :ref:`Excluded Ada Features`.

Procedures and functions that query the content of a container take the
container in parameter. For example, function ``Has_Element`` that queries if a
container has an element at a given position is declared as follows:

.. code-block:: ada

   function Has_Element (Container : T; Position : Cursor) return Boolean;

This is different from the API of controlled containers and bounded containers,
where it is sufficient to pass a cursor to these subprograms, as the cursor
holds a reference to the underlying container:

.. code-block:: ada

   function Has_Element (Position : Cursor) return Boolean;

Cursors of formal containers do not hold a reference to a specific container,
as this would otherwise introduce aliasing between container and cursor
variables, which is not supported in |SPARK|. See :ref:`Absence of
Interferences`. As a result, the same cursor can be applied to multiple
container objects.

For each container type, the library provides model functions that are used to
annotate subprograms from the API. The different models supply different levels
of abstraction of the container’s functionalities. These model functions are
grouped in :ref:`Ghost Packages` named ``Formal_Model``.

The higher level view of a container is usually the mathematical structure of
element it represents. We use a sequence for ordered containers such as lists and
vectors and a mathematical map for imperative maps. This allows us to specify
the effects of a subprogram in a very high level way, not having to consider
cursors nor order of elements in a map:

.. code-block:: ada

   procedure Increment_All (L : in out List) with
     Post =>
       (for all N in 1 .. Length (L) =>
          Element (Model (L), N) = Element (Model (L)'Old, N) + 1);

   procedure Increment_All (S : in out Map) with
     Post =>
       (for all K of Model (S)'Old => Has_Key (Model (S), K))
          and
       (for all K of Model (S) =>
          Has_Key (Model (S)'Old, K)
            and Get (Model (S), K) = Get (Model (S)'Old, K) + 1);

For sets and maps, there is a lower level model representing the underlying
order used for iteration in the container, as well as the actual values of
elements/keys. It is a sequence of elements/keys. We can use it if we want to
specify in ``Increment_All`` on maps that the order and actual values of keys
are preserved:

.. code-block:: ada

   procedure Increment_All (S : in out Map) with
     Post =>
       Keys (S) = Keys (S)'Old
         and
       (for all K of Model (S) =>
          Get (Model (S), K) = Get (Model (S)'Old, K) + 1);

Finally, cursors are modeled using a functional map linking them to their
position in the container. For example, we can state that the positions of
cursors in a list are not modified by a call to ``Increment_All``:


.. code-block:: ada

   procedure Increment_All (L : in out List) with
     Post =>
       Positions (L) = Positions (L)'Old
         and
       (for all N in 1 .. Length (L) =>
          Element (Model (L), N) = Element (Model (L)'Old, N) + 1);


Switching between the different levels of model functions allows to express
precise considerations when needed without polluting upper level specifications.
For example, consider a variant of the ``List.Find`` function defined in the
API of formal containers, which returns a cursor holding the value searched if
there is one, and the special cursor ``No_Element`` otherwise:

.. literalinclude:: /gnatprove_by_example/examples/my_find.ads
   :language: ada
   :linenos:

The ghost functions mentioned above are specially useful in :ref:`Loop
Invariants` to refer to cursors, and positions of elements in the containers.
For example, here, ghost function ``Positions`` is used in the loop invariant to
query the position of the current cursor in the list, and ``Model`` is used to
specify that the value searched is not contained in the part of the container
already traversed (otherwise the loop would have exited):

.. literalinclude:: /gnatprove_by_example/examples/my_find.adb
   :language: ada
   :linenos:

|GNATprove| proves that function ``My_Find`` implements its specification:

.. literalinclude:: /gnatprove_by_example/results/my_find.prove
   :language: none

Quantification over Formal Containers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:ref:`Quantified Expressions` can be used over the content of a formal
container to express that a property holds for all elements of a container
(using ``for all``) or that a property holds for at least one element of a
container (using ``for some``).

For example, we can express that all elements of a formal list of integers are
prime as follows:

.. code-block:: ada

   (for all Cu in My_List => Is_Prime (Element (My_List, Cu)))

On this expression, the |GNAT Pro| compiler generates code that iterates over
``My_List`` using the functions ``First``, ``Has_Element`` and ``Next`` given
in the ``Iterable`` aspect applying to the type of formal lists, so the
quantified expression above is equivalent to:

.. code-block:: ada

   declare
      Cu     : Cursor_Type := First (My_List);
      Result : Boolean := True;
   begin
      while Result and then Has_Element (My_List, Cu) loop
         Result := Is_Prime (Element (My_List, Cu));
         Cu     := Next (My_List, Cu);
      end loop;
   end;

where ``Result`` is the value of the quantified expression. See |GNAT Pro|
Reference Manual for details on aspect ``Iterable``.

.. _SPARK Lemma Library:

SPARK Lemma Library
-------------------

As part of the |SPARK| product, a library of lemmas is available through the
project file :file:`<spark-install>/lib/gnat/spark_lemmas.gpr`. To use this
library in a program, you need to add a corresponding dependency in your
project file, for example:

.. code-block:: gpr

  with "spark_lemmas";
  project My_Project is
     ...
  end My_Project;

You may need to update the environment variable ``GPR_PROJECT_PATH`` for the
lemma library project to be found by GNAT compiler, as described in
:ref:`Installation of GNATprove`.

You also need to set the environment variable ``SPARK_LEMMAS_OBJECT_DIR`` to
the absolute path of the object directory where you want compilation and
verification artefacts for the lemma library to be created. This should be an
absolute path (not a relative one) otherwise these artefacts will be created
inside you |SPARK| install.

Finally, if you instantiate in your code a generic from the lemma library, you
also need to pass ``-gnateDSPARK_BODY_MODE=Off`` as a compilation switch for
these generic units.

This library consists in a set of ghost null procedures with contracts (called
`lemmas`). Here is an example of such a lemma:

.. code-block:: ada

   procedure Lemma_Div_Is_Monotonic
     (Val1  : Int;
      Val2  : Int;
      Denom : Pos)
   with
     Global => null,
     Pre  => Val1 <= Val2,
     Post => Val1 / Denom <= Val2 / Denom;

whose body is simply a null procedure:

.. code-block:: ada

   procedure Lemma_Div_Is_Monotonic
     (Val1  : Int;
      Val2  : Int;
      Denom : Pos)
   is null;

This procedure is ghost (as part of a ghost package), which means that the
procedure body and all calls to the procedure are compiled away when producing
the final executable without assertions (when switch `-gnata` is not set). On
the contrary, when compiling with assertions for testing (when switch `-gnata`
is set) the precondition of the procedure is executed, possibly detecting
invalid uses of the lemma. However, the main purpose of such a lemma is to
facilitate automatic proof, by providing the prover specific properties
expressed in the postcondition. In the case of ``Lemma_Div_Is_Monotonic``, the
postcondition expresses an inequality between two expressions. You may use this
lemma in your program by calling it on specific expressions, for example:

.. code-block:: ada

   R1 := X1 / Y;
   R2 := X2 / Y;
   Lemma_Div_Is_Monotonic (X1, X2, Y);
   --  at this program point, the prover knows that R1 <= R2
   --  the following assertion is proved automatically:
   pragma Assert (R1 <= R2);

Note that the lemma may have a precondition, stating in which contexts the
lemma holds, which you will need to prove when calling it. For example, a
precondition check is generated in the code above to show that ``X1 <=
X2``. Similarly, the types of parameters in the lemma may restrict the contexts
in which the lemma holds. For example, the type ``Pos`` for parameter ``Denom``
of ``Lemma_Div_Is_Monotonic`` is the type of positive integers. Hence, a range
check may be generated in the code above to show that ``Y`` is positive.

All the lemmas provided in the SPARK lemma library have been proved either
automatically or using Coq interactive prover. The Why3 session file recording
all proofs, as well as the individual Coq proof scripts, are available as part
of the |SPARK| product under directory
:file:`<spark-install>/lib/gnat/proof`. For example, the proof of lemma
``Lemma_Div_Is_Monotonic`` is a Coq proof of the mathematical property (in Coq
syntax):

.. image:: /static/div_is_monotonic_in_coq.png
   :width: 400 px
   :align: center
   :alt: Property that division is monotonic in Coq syntax

Currenly, the SPARK lemma library provides the following lemmas:

* Lemmas on signed integer arithmetic in file ``spark-arithmetic_lemmas.ads``,
  that are instantiated for 32 bits signed integers (``Integer``) in file
  ``spark-integer_arithmetic_lemmas.ads`` and for 64 bits signed integers
  (``Long_Integer``) in file ``spark-long_integer_arithmetic_lemmas.ads``.

* Lemmas on modular integer arithmetic in file
  ``spark-mod_arithmetic_lemmas.ads``, that are instantiated for 32 bits
  modular integers (``Interfaces.Unsigned_32``) in file
  ``spark-mod32_arithmetic_lemmas.ads`` and for 64 bits modular integers
  (``Interfaces.Unsigned_64``) in file ``spark-mod64_arithmetic_lemmas.ads``.

* GNAT-specific lemmas on fixed-point arithmetic in file
  ``spark-fixed_point_arithmetic_lemmas.ads``, that need to be instantiated by
  the user for her specific fixed-point type.

* Lemmas on floating point arithmetic in file
  ``spark-floating_point_arithmetic_lemmas.ads``, that are instantiated for
  single-precision floats (``Float``) in file
  ``spark-float_arithmetic_lemmas.ads`` and for double-precision floats
  (``Long_Float``) in file ``spark-long_float_arithmetic_lemmas.ads``.

* Lemmas on unconstrained arrays in file
  ``spark-unconstrained_array_lemmas.ads``, that need to be instantiated by the
  user for her specific type of index and element, and specific ordering
  function between elements.

To apply lemmas to signed or modular integers of different types than the ones
used in the instances provided in the library, just convert the expressions
passed in arguments, as follows:

.. code-block:: ada

   R1 := X1 / Y;
   R2 := X2 / Y;
   Lemma_Div_Is_Monotonic (Integer(X1), Integer(X2), Integer(Y));
   --  at this program point, the prover knows that R1 <= R2
   --  the following assertion is proved automatically:
   pragma Assert (R1 <= R2);

.. _Higher Order Function Library:

Higher Order Function Library
-----------------------------

The SPARK product also includes a library of higher order functions for
unconstrained arrays. It is available using the same project file as the
:ref:`SPARK Lemma Library`.

This library consists in a set of generic entities defining usual operations on
arrays. As an example, here is a generic function for the map higher-level
function on arrays. It applies a given function ``F`` to each element of an
array, returning an array of results in the same order.

.. code-block:: ada

   generic
      type Index_Type is range <>;
      type Element_In is private;
      type Array_In is array (Index_Type range <>) of Element_In;

      type Element_Out is private;
      type Array_Out is array (Index_Type range <>) of Element_Out;

      with function Init_Prop (A : Element_In) return Boolean;
      --  Potential additional constraint on values of the array to allow Map

      with function F (X : Element_In) return Element_Out;
      --  Function that should be applied to elements of Array_In

   function Map (A : Array_In) return Array_Out with
     Pre  => (for all I in A'Range => Init_Prop (A (I))),
     Post => Map'Result'First = A'First
     and then Map'Result'Last = A'Last
     and then (for all I in A'Range =>
                 Map'Result (I) = F (A (I)));

This function can be instantiated by providing two unconstrained array types
ranging over the same index type and a function ``F`` mapping a component of the
first array type to a component of the second array type. Additionally, a
constraint ``Init_Prop`` can be supplied for the components of the first array
to be allowed to apply ``F``. If no such constraint is needed, ``Init_Prop`` can
be instantiated with an always ``True`` function.

.. code-block:: ada

   type Nat_Array is array (Positive range <>) of Natural;

   function Small_Enough (X : Natural) return Boolean is
     (X < Integer'Last);

   function Increment_One (X : Integer) return Integer is (X + 1) with
     Pre => X < Integer'Last;

   function Increment_All is new SPARK.Higher_Order.Map
     (Index_Type  => Positive,
      Element_In  => Natural,
      Array_In    => Nat_Array,
      Element_Out => Natural,
      Array_Out   => Nat_Array,
      Init_Prop   => Small_Enough,
      F           => Increment_One);

The ``Increment_All`` function above will take as an argument an array of
natural numbers small enough to be incremented and will return an array
containing the result of incrementing each number by one:

.. code-block:: ada

   function Increment_All (A : Nat_Array) return Nat_Array with
     Pre  => (for all I in A'Range => Small_Enough (A (I))),
     Post => Increment_All'Result'First = A'First
     and then Increment_All'Result'Last = A'Last
     and then (for all I in A'Range =>
                 Increment_All'Result (I) = Increment_One (A (I)));

Currently, the higher-order function library provides the following functions:

* Map functions over unconstrained one-dimensional arrays in file
  ``spark-higher_order.ads``. These include both in place and functional
  map subprograms, with and without an additional position parameter.

* Fold functions over unconstrained one-dimensional and two-dimensional arrays
  in file ``spark-higher_order-fold.ads``. Both left to right and right to left
  fold functions are available for one-dimensional arrays. For two-dimensional
  arrays, fold functions go on a line by line, left to right, top-to-bottom
  way. For ease of use, these functions have been instantiated for the most
  common cases. ``Sum`` and ``Sum_2`` respectively compute the sum of all the
  elements of a one-dimensional or two-dimensional array, and ``Count`` and
  ``Count_2`` the number of elements with a given ``Choose`` property.

.. note::

   Unlike the :ref:`SPARK Lemma Library`, these generic functions are
   not verified once and for all as their correction depends on the functions
   provided at each instance. As a result, each instance should be verified by
   running the SPARK tools.

.. _Input-Output Libraries:

Input-Output Libraries
----------------------

The following text is about ``Ada.Text_IO`` and its child packages,
``Ada.Text_IO.Integer_IO``, ``Ada.Text_IO.Modular_IO``,
``Ada.Text_IO.Float_IO``, ``Ada.Text_IO.Fixed_IO``,
``Ada.Text_IO.Decimal_IO`` and ``Ada.Text_IO.Enumeration_IO``.

The effect of functions and procedures of input-output units is
partially modelled. This means in particular:

* that SPARK functions cannot directly call procedures that do
  input-output. The solution is either to transform them into
  procedures, or to hide the effect from GNATprove (if not relevant
  for analysis) by wrapping the standard input-output procedures in
  procedures with an explicit ``Global => null`` and body with
  ``SPARK_Mode => Off``.

  .. code-block:: ada

     with Ada.Text_IO;

     function Foo return Integer is

        procedure Put_Line (Item : String) with
          Global => null;

        procedure Put_Line (Item : String) with
          SPARK_Mode => Off
        is
        begin
           Ada.Text_IO.Put_Line (Item);
        end Put_Line;

     begin
        Put_Line ("Hello, world!");
        return 0;
     end Foo;

* SPARK procedures that call input-output subprograms need to reflect
  these effects in their Global/Depends contract if they have one.

  .. code-block:: ada

    with Ada.Text_IO;

    procedure Foo with
      Global => (Input  => Var,
                 In_Out => Ada.Text_IO.File_System)
    is
    begin
       Ada.Text_IO.Put_Line (Var);
    end Foo;

    procedure Bar is
    begin
       Ada.Text_IO.Put_Line (Var);
    end Bar;

In the examples above, procedure ``Foo`` and ``Bar`` have the same
body, but their declarations are different. Global contracts have to
be complete or not present at all. In the case of ``Foo``, it has an
``Input`` contract on ``Var`` and an ``In_Out`` contract on
``File_System``, an abstract state from ``Ada.Text_IO``. Without the
latter contract, a high message would be raised when running
GNATprove. Global contracts will be automatically generated for
``Bar`` by flow analysis if this is user code. Both declarations are
accepted by SPARK.

State Abstraction and Global Contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The abstract state ``File_System`` is used to model the memory on
the system and the file handles (``Line_Length``, ``Col``, etc.). This
is explained by the fact that almost every procedure in ``Text_IO``
that actually modifies attributes of the ``File_Type`` parameter has
``in File_Type`` as a parameter and not ``in out``. This would be
inconsistent with SPARK rules without the abstract state.

All functions and procedures are annoted with Global, and Pre, Post if
necessary. The Global contracts are most of the time ``In_Out`` for
``File_System``, even in ``Put`` or ``Get`` procedures that update the
current column and/or line. Functions have an ``Input`` global
contract. The only functions with ``Global => null`` are the functions
``Get`` and ``Put`` in the generic packages that have a similar
behaviour as sprintf and sscanf.

Functions and Procedures Removed in SPARK
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Some functions and procedures are removed from SPARK usage because they
are not consistent with SPARK rules:

#. Aliasing

   The functions ``Current_Input``, ``Current_Output``,
   ``Current_Error``, ``Standard_Input``, ``Standard_Output`` and
   ``Standard_Error`` are turned off in ``SPARK_Mode`` because they
   create aliasing, by returning the corresponding file.

   ``Set_Input``, ``Set_Output`` and ``Set_Error`` are turned off
   because they also create aliasing, by assigning a ``File_Type``
   variable to ``Current_Input`` or the other two.

   It is still possible to use ``Set_Input`` and the 3 others to make
   the code clearer. This is doable by calling ``Set_Input`` in a
   different subprogram whose body has ``SPARK_Mode => Off``. However,
   it is necessary to check that the file is open and the mode is
   correct, because there are no checks made on procedures that do not
   take a file as a parameter (i.e. implicit, so it will write to/read
   from the current output/input).

#. ``Get_Line`` function

   The function ``Get_Line`` is disabled in SPARK because it is a
   function with side effects. Even with the ``Volatile_Function``
   attribute, it is not possible to model its action on the files
   and global variables in SPARK. The function is very convenient
   because it returns an unconstrained string, but a workaround is
   possible by constructing the string with a buffer:

 .. code-block:: ada

    with Ada.Text_IO;
    with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

    procedure Echo is
       Unb_Str : Unbounded_String := Null_Unbounded_String;
       Buffer  : String (1 .. 1024);
       Last    : Natural := 1024;
    begin

       while Last = 1024 loop
          Ada.Text_IO.Get_Line (Buffer, Last);
          exit when Last > Natural'Last - Length (Unb_Str);
          Unb_Str := Unb_Str & Buffer (1 .. Last);
       end loop;

       declare
          Str : String := To_String (Unb_Str);
       begin
          Ada.Text_IO.Put_Line (Str);
       end;
    end Echo;

Errors Handling
^^^^^^^^^^^^^^^

``Status_Error`` (due to a file already open/not open) and ``Mode_Error`` are fully
handled.

Except for ``Layout_Error``, which is a special case of a partially
handled error and explained in a few lines below, all other errors are
not handled:

-  ``Use_Error`` is related to the external environment.

-  ``Name_Error`` would require to check availability on disk beforehand.

-  ``End_Error`` is raised when a file terminator is read while running
   the procedure.

For an ``Out_File``, it is possible to set a ``Line_Length`` and
``Page_Length``. When writing in this file, the procedures will add
Line markers and Page markers each ``Line_Length`` characters or
``Page_Length`` lines respectively. ``Layout_Error`` occurs when
trying to set the current column or line to a value that is greater
than ``Line_Length`` or ``Page_Length`` respectively. This error is
handled when using ``Set_Col`` or ``Set_Line`` procedures.

However, this error is not handled when no ``Line_Length`` or
``Page_Length`` has been specified, e.g, if the lines are unbounded,
it is possible to have a ``Col`` greater than ``Count'Last`` and
therefore have a ``Layout_Error`` raised when calling ``Col``.

Not only the handling is partial, but it is also impossible to prove
preconditions when working with two files or more. Since
``Line_Length`` etc. attributes are stored in the ``File_System``, it
is not posible to prove that the ``Line_Length`` of ``File_2`` has not
been modified when running any procedure that do input-output on ``File_1``.
