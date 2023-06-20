SPARK Libraries
===============

The units described here have their spec in SPARK (with ``SPARK_Mode => On``
specified on the spec), more rarely their body in SPARK as well.

Subprograms in these units fall into one of the following categories:

- Subprograms which should always return without error or exception if their
  precondition is respected.

- Procedures marked with the annotation ``Exceptional_Cases``.
  This corresponds to the possibility of exception in the procedure,
  even when its precondition is respected.

- Functions marked with ``SPARK_Mode => Off`` which cannot be called from SPARK
  code.

.. index:: SPARK Library

SPARK Library
-------------

As part of the |SPARK| product, several libraries are available through the
project file :file:`<spark-install>/lib/gnat/sparklib.gpr` (or through the
project file :file:`<spark-install>/lib/gnat/sparklib_light.gpr` in
an environment without units ``Ada.Numerics.Big_Numbers.Big_Integers`` and
``Ada.Numerics.Big_Numbers.Big_Reals``). Header files of the SPARK library are available
through :menuselection:`Help --> SPARK --> SPARKlib` menu item in GNAT Studio. To
use this library in a program, you need to add a corresponding dependency in
your project file, for example:

.. code-block:: gpr

  with "sparklib";
  project My_Project is
     ...
  end My_Project;

.. index:: GPR_PROJECT_PATH; for SPARK library

You may need to update the environment variable ``GPR_PROJECT_PATH`` for the
lemma library project to be found by GNAT compiler, as described in
:ref:`Installation of GNATprove`.

You also need to set the environment variable ``SPARKLIB_OBJECT_DIR`` to
the absolute path of the object directory where you want compilation and
verification artefacts for the SPARK library to be created. This should be an
absolute path (not a relative one) otherwise these artefacts will be created
inside your |SPARK| install.

Finally, if you instantiate in your code a generic from the SPARK library, you
also need to pass ``-gnateDSPARK_BODY_MODE=Off`` as a compilation switch for
these generic units.

.. index:: Big_Numbers

Big Numbers Library
-------------------

Annotations such as preconditions, postconditions, assertions, loop invariants,
are analyzed by |GNATprove| with the exact same meaning that they have during
execution. In particular, evaluating the expressions in an annotation may raise
a run-time error, in which case |GNATprove| will attempt to prove that this
error cannot occur, and report a warning otherwise.

In |SPARK|, scalar types such as integer and floating point types are bounded
machine types, so arithmetic computations over them can lead to overflows when
the result does not fit in the bounds of the type used to hold it. In some
cases, it is convenient to express properties in annotations as they would be
expressed in mathematics, where quantities are unbounded, for example:

.. code-block:: ada

 function Add (X, Y : Integer) return Integer with
   Pre  => X + Y in Integer,
   Post => Add'Result = X + Y;

The precondition of ``Add`` states that the result of adding its two parameters
should fit in type ``Integer``. Unfortunately, evaluating this expression will
fail an overflow check, because the result of ``X + Y`` is stored in a temporary
of type ``Integer``.

To alleviate this issue, it is possible to use the standard library for big
numbers. It contains support for:

* Unbounded integers in ``SPARK.Big_Integers``.

* Unbounded rational numbers in ``SPARK.Big_Reals``.

Theses libraries define representations for big numbers and basic arithmetic
operations over them, as well as conversions from bounded scalar types such as
floating point numbers or integer types. Conversion from an integer to a big
integer is provided by:

* function ``To_Big_Integer`` in ``SPARK.Big_Integers`` for
  type ``Integer``

* function ``To_Big_Integer`` in generic package ``Signed_Conversions`` in
  ``SPARK.Big_Integers`` for all other signed integer types

* function ``To_Big_Integer`` in generic package ``Unsigned_Conversions`` in
  ``SPARK.Big_Integers`` for modular integer types

Similarly, the same packages define a function ``From_Big_Integer`` to convert
from a big integer to an integer. A function ``To_Real`` in
``SPARK.Big_Reals`` converts from type ``Integer`` to a big
real and function ``To_Big_Real`` in the same package converts from a big
integer to a big real.

Though these operations do not have postconditions, they are interpreted by
|GNATprove| as the equivalent operations on mathematical integers and real
numbers. This allows to benefit from precise support on code using them. Note
that the corresponding Ada libraries ``Ada.Numerics.Big_Numbers.Big_Integers``
and ``Ada.Numerics.Big_Numbers.Big_Reals`` will be handled in the same way, but
might be not available under specific runtimes. It is preferable to use the
units from the SPARK library instead, or use
``Ada.Numerics.Big_Numbers.Big_Integer_Ghost``.

.. note::

   Some functionality of the library are not precisely supported. This includes
   in particular conversions to and from strings, conversions of ``Big_Real`` to
   fixed-point or floating-point types, and ``Numerator`` and ``Denominator``
   functions.

The big number library can be used both in annotations and in actual code, as
it is executable, though of course, using it in production code means incurring
its runtime costs. It can be considered a good trade-off to only use it in
contracts, if they are disabled in production builds. For example, we can
rewrite the precondition of our ``Add`` function with big integers to avoid
overflows:

.. code-block:: ada

   function Add (X, Y : Integer) return Integer with
     Pre  => In_Range (To_Big_Integer (X) + To_Big_Integer (Y),
                       Low  => To_Big_Integer (Integer'First),
                       High => To_Big_Integer (Integer'Last)),
     Post => Add'Result = X + Y;

As a more advanced example, it is also possible to introduce a ghost model for
numerical computations on floating point numbers as a mathematical real
number so as to be able to express properties about rounding errors. In the
following snippet, we use the ghost variable ``M`` as a model of the
floating point variable ``Y``, so we can assert that the result of our
floating point calculations are not too far from the result of the same
computations on real numbers.

.. code-block:: ada

   declare
      package Float_Convs is new Float_Conversions (Num => Float);
      --  Introduce conversions to and from values of type Float

      subtype Small_Float is Float range -100.0 .. 100.0;

      function Init return Small_Float with Import;
      --  Unknown initial value of the computation

      X : constant Small_Float := Init;
      Y : Float := X;
      M : Big_Real := Float_Convs.To_Big_Real (X) with Ghost;
      --  M is used to mimic the computations done on Y on real numbers

   begin
      Y := Y * 100.0;
      M := M * Float_Convs.To_Big_Real (100.0);
      Y := Y + 100.0;
      M := M + Float_Convs.To_Big_Real (100.0);

      pragma Assert
        (In_Range (Float_Convs.To_Big_Real (Y) - M,
                   Low  => Float_Convs.To_Big_Real (- 0.001),
                   High => Float_Convs.To_Big_Real (0.001)));
      --  The rounding errors introduced by the floating-point computations
      --  are not too big.
   end;

.. index:: functional containers

Functional Containers Library
-----------------------------

To model complex data structures, one often needs simpler,
mathematical like containers. The mathematical containers provided in
the |SPARK| library (see the :ref:`SPARK Library`) are unbounded and
may contain indefinite elements. However, they are controlled and thus
not usable in every context. So that these containers can be used safely,
we have made them functional, that is, no primitives are provided which
would allow modifying an existing container. Instead, their API features
functions creating new containers from existing ones. As an example,
functional containers provide no ``Insert`` procedure but rather a function
``Add`` which creates a new container with one more element than its parameter:

.. code-block:: ada

    function Add (C : Container; E : Element_Type) return Container;

As a consequence, these containers are highly inefficient. Thus, they should in
general be used in ghost code and annotations so that they can be removed from
the final executable.

There are 5 functional containers, which are part of the |SPARK| library:

* ``SPARK.Containers.Functional.Infinite_Sequences``
* ``SPARK.Containers.Functional.Maps``
* ``SPARK.Containers.Functional.Multisets``
* ``SPARK.Containers.Functional.Sets``
* ``SPARK.Containers.Functional.Vectors``

Sequences defined in ``Functional.Vectors`` are no more than ordered collections
of elements. In an Ada like manner, the user can choose the range used to index
the elements:


.. code-block:: ada

    function Length (S : Sequence) return Count_Type;
    function Get (S : Sequence; N : Index_Type) return Element_Type;

The sequences defined in ``Functional.Infinite_Sequences`` behave as the one of
``Functional.Vectors``. The difference between them lies in the fact that the
inifinte one are indexed by mathematical integers.

.. code-block:: ada

    function Length (Container : Sequence) return Big_Natural;
    function Get (Container : Sequence; Position  : Big_Integer) return Element_Type;

Functional sets offer standard mathematical set functionalities such as
inclusion, union, and intersection. They are neither ordered nor hashed:


.. code-block:: ada

    function Contains (S : Set; E : Element_Type) return Boolean;
    function "<=" (Left : Set; Right : Set) return Boolean;

Functional maps offer a dictionary between any two types of elements:

.. code-block:: ada

    function Has_Key (M : Map; K : Key_Type) return Boolean;
    function Get (M : Map; K : Key_Type) return Element_Type;

Multisets are mathematical sets associated with a number of occurrences:

.. code-block:: ada

   function Nb_Occurence (S : Multiset; E : Element_Type) return Big_Natural;
   function Cardinality (S : Multiset) return Big_Natural;

Each functional container type supports quantification over its elements
(or keys for functional maps).

These containers can easily be used to model user defined data structures. They
were used to this end to annotate and verify a package of allocators (see
the `allocators` example provided with a SPARK installation). In
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

   Instances of container packages, both functional and formal, are subjected
   to particular constraints which are necessary for the contracts on the
   instance to be correct. For example, container primitives don't comply with
   the ownership policy of SPARK if element or key types are ownership types.
   These constraints are verified specifically each time a container
   package is instantiated. For some of these checks, it is
   possible for the user to help the proof tool by providing some lemmas
   at instantiation. It is the case in particular for the
   constraints coming from the Ada reference manual on the container
   packages (that "=" is an equivalence relation, or that "<" is a strict
   weak order in particular). These lemmas appear in the library as additional
   ghost generic formal parameters.

The functional sets, maps, sequences, and vectors have child packages providing
higher order functions:

* ``SPARK.Containers.Functional.Infinite_Sequences.Higher_Order``
* ``SPARK.Containers.Functional.Maps.Higher_Order``
* ``SPARK.Containers.Functional.Sets.Higher_Order``
* ``SPARK.Containers.Functional.Vectors.Higher_Order``

These functions take as parameters access-to-functions that compute some
information about an element of the container and apply it to all elements in
a generic way. As an example, here is the function ``Count`` for functional
sets. It counts the number of elements in the set with a given property. The
property is provided by its input access-to-function parameter ``Test``:

.. code-block:: ada

   function Count
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
      return Big_Natural
   --  Count the number of elements on which the input Test function returns
   --  True. Count can only be used with Test functions which return the same
   --  value on equivalent elements.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Eq_Compatible (S, Test),
     Post     => Count'Result <= Length (S);

All the higher order functions are annotated with
``Higher_Order_Specialization`` (see
:ref:`Using Annotations to Request Specialized Handling For Higher Order Functions`)
so they can be used even with functions which read global data as parameters.

.. index:: formal containers

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
  ``SPARK.Containers.Formal.Unbounded_Sets``. They define containers as
  controlled tagged types, so that memory for the container is automatic
  reallocated during assignment and automatically freed when the container
  object's scope ends.
* The bounded containers not using dynamic allocation, for example
  ``SPARK.Containers.Fromal.Vectors``. They define containers as discriminated
  tagged types, so that the memory for the container can be reserved at
  initialization.

Although bounded containers are better suited to critical software development,
neither controlled containers nor bounded containers can be used in |SPARK|,
because their API does not lend itself to adding suitable contracts (in
particular preconditions) ensuring correct usage in client code.

The formal containers are a variation of the standard containers with API
changes that allow adding suitable contracts, so that |GNATprove| can prove
that client code manipulates containers correctly. There are 12 formal
containers, which are part of the |SPARK| library.

Among them, 6 are bounded and definite:

* ``SPARK.Containers.Formal.Vectors``
* ``SPARK.Containers.Formal.Doubly_Linked_Lists``
* ``SPARK.Containers.Formal.Hashed_Sets``
* ``SPARK.Containers.Formal.Ordered_Sets``
* ``SPARK.Containers.Formal.Hashed_Maps``
* ``SPARK.Containers.Formal.Ordered_Maps``

The 6 others are unbounded and indefinite but are controlled:

* ``SPARK.Containers.Formal.Unbounded_Vectors``
* ``SPARK.Containers.Formal.Unbounded_Doubly_Linked_Lists``
* ``SPARK.Containers.Formal.Unbounded_Hashed_Sets``
* ``SPARK.Containers.Formal.Unbounded_Ordered_Sets``
* ``SPARK.Containers.Formal.Unbounded_Hashed_Maps``
* ``SPARK.Containers.Formal.Unbounded_Ordered_Maps``

Bounded definite formal containers can only contain definite objects (objects
for which the compiler can compute the size in memory, hence not ``String`` nor
``T'Class``). They do not use dynamic allocation. In particular, they cannot
grow beyond the bound defined at object creation.

Unbounded indefinite formal containers can contain indefinite objects. They use
dynamic allocation both to allocate memory for their elements, and to expand
their internal block of memory when it is full.

.. note::

    The capacity of unbounded containers is not set using a
    discriminant. Instead, it is implicitly set to it maximum value. All the
    required memory is not reserved at declaration. As all the formal
    containers are internally indexed by ``Count_Type``, their maximum size is
    ``Count_Type'Last``.

Modified API of Formal Containers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The visible specification of formal containers is in |SPARK|, with suitable
contracts on subprograms to ensure correct usage, while their private part
and implementation is not in |SPARK|. Hence, |GNATprove| can be used to prove
correct usage of formal containers in client code, but not to prove that formal
containers implement their specification.

Procedures ``Update_Element`` or ``Query_Element`` that iterate over a
container are not defined on formal containers. The effect of these procedures
could not be precisely described in their contracts as there is no way to
refer to the contract of their access-to-procedure parameter.

Procedures and functions that query the content of a container take the
container in parameter. For example, function ``Has_Element`` that queries if a
container has an element at a given position is declared as follows:

.. code-block:: ada

   function Has_Element (Container : T; Position : Cursor) return Boolean;

This is different from the API of standard containers,
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

.. literalinclude:: /examples/ug__my_find/my_find.ads
   :language: ada
   :linenos:

The ghost functions mentioned above are specially useful in :ref:`Loop
Invariants` to refer to cursors, and positions of elements in the containers.
For example, here, ghost function ``Positions`` is used in the loop invariant to
query the position of the current cursor in the list, and ``Model`` is used to
specify that the value searched is not contained in the part of the container
already traversed (otherwise the loop would have exited):

.. literalinclude:: /examples/ug__my_find/my_find.adb
   :language: ada
   :linenos:

|GNATprove| proves that function ``My_Find`` implements its specification:

.. literalinclude:: /examples/ug__my_find/test.out
   :language: none

.. note::

   Just like functional containers, the formal containers do not comply with
   the ownership policy of SPARK if element or key types are ownership types.
   These constraints are verified specifically each time a container package is
   instantiated.

.. index:: quantified-expression; over container

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

.. index:: lemma library

SPARK Lemma Library
-------------------

As part of the SPARK library (see :ref:`SPARK Library`), packages
declaring a set of ghost null procedures with contracts (called
`lemmas`) are distributed. Here is an example of such a lemma:

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

* Lemmas on signed integer arithmetic in file ``spark-lemmas-arithmetic.ads``,
  that are instantiated for 32 bits signed integers (``Integer``) in file
  ``spark-lemmas-integer_arithmetic.ads`` and for 64 bits signed integers
  (``Long_Integer``) in file ``spark-lemmas-long_integer_arithmetic.ads``.

* Lemmas on modular integer arithmetic in file
  ``spark-lemmas-mod_arithmetic.ads``, that are instantiated for 32 bits
  modular integers (``Interfaces.Unsigned_32``) in file
  ``spark-lemmas-mod32_arithmetic.ads`` and for 64 bits modular integers
  (``Interfaces.Unsigned_64``) in file ``spark-lemmas-mod64_arithmetic.ads``.

* GNAT-specific lemmas on fixed-point arithmetic in file
  ``spark-lemmas-fixed_point_arithmetic.ads``, that need to be instantiated by
  the user for her specific fixed-point type.

* Lemmas on floating point arithmetic in file
  ``spark-lemmas-floating_point_arithmetic.ads``, that are instantiated for
  single-precision floats (``Float``) in file
  ``spark-lemmas-float_arithmetic.ads`` and for double-precision floats
  (``Long_Float``) in file ``spark-lemmas-long_float_arithmetic.ads``.

* Lemmas on unconstrained arrays in file
  ``spark-lemmas-unconstrained_array.ads``, that need to be instantiated by the
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

Higher Order Function Library
-----------------------------

The SPARK product also includes a library of higher order functions
for unconstrained arrays. It is available using the |SPARK| library
(see :ref:`SPARK Library`).

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

.. index:: input-output

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

Finally, ``Layout_Error`` may be raised when calling ``Put`` to display the
value of a real number (floating-point or fixed-point) in a string output
parameter, which is not reflected currently in the precondition of ``Put`` as
no simple precondition can describe the required length in such a case.

.. index:: strings

Strings Libraries
-----------------

The following text is about ``Ada.Strings.Maps``, ``Ada.Strings.Fixed``,
``Ada.Strings.Bounded`` and ``Ada.Strings.Unbounded``.

Global contracts were added to non-pure packages, and pre/postconditions were
added to all SPARK subprograms to partially model their effects. In
particular:

* Effects of subprograms from ``Ada.Strings.Maps``, as specified in the Ada RM
  (A.4.2), are fully modeled through pre- and postconditions.

* Effects of most subprograms from ``Ada.Strings.Fixed`` are fully
  modeled through pre- and postconditions. Preconditions protect from
  exceptions specified in the Ada RM (A.4.3). Some procedures are not
  annotated with sufficient preconditions and may raise ``Length_Error`` when
  called with inconsistent parameters. They are annotated with an exceptional
  contract.

  Under their respective preconditions, the implementation of subprograms from
  ``Ada.Strings.Fixed`` is proven with |GNATprove| to be free from run-time
  errors and to comply with their postcondition, except for procedure ``Move``
  and those procedures based on ``Move``: ``Delete``, ``Head``, ``Insert``,
  ``Overwrite``, ``Replace_Slice``, ``Tail`` and ``Trim`` (but the
  corresponding functions are proved).

* Effects of subprograms from ``Ada.Strings.Bounded`` are fully modeled through
  pre- and postconditions. Preconditions protect from exceptions specified in
  the Ada RM (A.4.4).

  Under their respective preconditions, the implementation of subprograms from
  ``Ada.Strings.Bounded`` is proven with |GNATprove| to be free from run-time
  errors, and except for subprograms ``Insert``, ``Overwrite`` and
  ``Replace_Slice``, to comply with their postcondition.

* Effects of subprograms from ``Ada.Strings.Unbounded`` are partially
  modeled. Postconditions state properties on the Length of the strings only
  and not on their content. Preconditions protect from exceptions specified in
  the Ada RM (A.4.5).

* The procedure ``Free`` in ``Ada.Strings.Unbounded`` is not in SPARK as it
  could be wrongly called by the user on a pointer to the stack.

Inside these packages, ``Translation_Error`` (in ``Ada.Strings.Maps``),
``Index_Error`` and ``Pattern_Error`` are fully handled.

``Length_Error`` is fully handled in ``Ada.Strings.Bounded`` and
``Ada.Strings.Unbounded`` and in functions from ``Ada.Strings.Fixed``.

However, in the procedure ``Move`` and the procedures based on it except for
``Delete`` and ``Trim`` (``Head``, ``Insert``, ``Overwrite``, ``Replace_Slice``
and ``Tail``) from ``Ada.Strings.Fixed``, ``Length_Error`` may be raised under
certain conditions. This is related to the call to ``Move``. Each call of these
subprograms can be preceded with a pragma Assert to check that the actual
parameters are consistent, when parameter ``Drop`` is set to ``Error`` and the
``Source`` is longer than ``Target``.

 .. code-block:: ada

    --  From the Ada RM for Move: "The Move procedure copies characters from
    --  Source to Target.
    --
    --  ...
    --
    --  If Source is longer than Target, then the effect is based on Drop.
    --
    --  ...
    --
    --  * If Drop=Error, then the effect depends on the value of the Justify
    --    parameter and also on whether any characters in Source other than Pad
    --    would fail to be copied:
    --
    --    * If Justify=Left, and if each of the rightmost
    --      Source'Length-Target'Length characters in Source is Pad, then the
    --      leftmost Target'Length characters of Source are copied to Target.
    --
    --    * If Justify=Right, and if each of the leftmost
    --      Source'Length-Target'Length characters in Source is Pad, then the
    --      rightmost Target'Length characters of Source are copied to Target.
    --
    --    * Otherwise, Length_Error is propagated.".
    --
    --  Here, Move will be called with Drop = Error, Justify = Left and
    --  Pad = Space, so we add the following assertion before the call to Move.

    pragma Assert
     (if Source'Length > Target'Length then
        (for all J in 1 .. Source'Length - Target'Length =>
           (Source (Source'Last - J + 1) = Space)));

    Move (Source  => Source,
          Target  => Target,
          Drop    => Error,
          Justify => Left,
          Pad     => Space);

.. index:: c-strings

C Strings Interface
-------------------

``Interfaces.C.Strings`` is a library that provides an Ada interface to
allocate, reference, update and free C strings.

The provided preconditions protect users from getting
``Dereference_Error`` and ``Update_Error``. However, those
preconditions do not protect against ``Storage_Error``.

All subprograms are annotated with Global contracts. To model the
effects of the subprograms on the allocated memory, an abstract state
``C_Memory`` is defined. Since ``chars_ptr`` is an access type that is
hidden from |SPARK| (it is a private type and the private part of
``Interfaces.C.Strings`` has ``SPARK_Mode => Off``), the user could
create aliases that SPARK would not be able to see. Hence, we consider
that calling ``Update`` on any ``chars_ptr`` modifies the allocated
memory, ``C_Memory``, so that the effects of potential aliases are
modelled correctly.

Additionally, some subprograms are annotated with ``SPARK_Mode => Off``:

*  ``To_Chars_Ptr``: This function creates an alias, thus it is not
   compatible with |SPARK|.

*  ``Free``: There is no way for |SPARK| to know whether or not it is
   safe to deallocate these pointers. They might not be allocated on
   the heap or there might be some aliases, which could lead to
   dangling pointers.

Finally, the two functions used to allocate memory to create
``chars_ptr`` objects are annotated with the ``Volatile_Function``
attribute. Indeed, calling those functions twice in a row with the
same parameters would return different objects.

.. index:: address-to-access-conversion

Addresses to Access Conversions
-------------------------------

The run-time library ``System.Address_To_Access_Conversions`` enables
the user to convert ``System.Address_Type`` values to general access-to-object
types. The conversions are subject to the same rules as
``Unchecked_Conversion`` between such types (see :ref:`Data Validity`),
that is:

* ``To_Pointer`` is allowed in |SPARK| and annotated with ``Global =>
  null``. On a call to this function, |GNATprove| will emit warnings
  to ensure that the designated data has no aliases and is initialized.

* ``To_Address`` is forbidden in |SPARK| because it does not handle
  addresses.

Cut Operations
--------------

The |SPARK| product also includes boolean cut operations that can be used to
manually help the proof of complicated assertions. These operations are
provided as functions in a library but are handled in a specific way by
|GNATprove|. They can be found in the ``SPARK.Cut_Operations`` package which
is available using the same project file as the :ref:`SPARK Lemma Library`.

This library provides two functions named ``By`` and ``So`` which are handled
in the following way:

*  If ``A`` and ``B`` are two boolean expressions, proving ``By (A, B)``
   requires proving ``B``, the premise, and then ``A`` assuming ``B``, the
   side-condition. When ``By (A, B)`` is assumed on the other hand, |GNATprove|
   only assumes ``A``. The proposition ``B`` is used for the proof of ``A``,
   but is not visible afterward.

*  If ``A`` and ``B`` are two boolean expressions, proving ``So (A, B)``
   requires proving ``A``, the premise, and then ``B`` assuming ``A``, the
   side-condition. When ``So (A, B)`` is assumed both ``A`` and ``B`` are
   assumed to be true.

This allows to introduce intermediate assertions to help the proof of some
part of an assertion by still controlling in a precise way what is added to the
enclosing context. This is interesting when doing complex proofs when the
size of the proof context (the amount of information known at a given program
point) is an issue.

In the example below, ``By`` is used to add the intermediate property ``B (I)``
in the proof of ``C (I)`` from ``A (I)``:

 .. code-block:: ada

  with SPARK.Cut_Operations; use SPARK.Cut_Operations;

  procedure Main with SPARK_Mode is
     function A (I : Integer) return Boolean with Import;
     function B (I : Integer) return Boolean with Import,
       Post => B'Result and then (if A (I) then C (I));
     function C (I : Integer) return Boolean with Import;
  begin
     pragma Assume (for all I in 1 .. 100 => A (I));
     pragma Assert (for all I in 1 .. 100 => By (C (I), B (I)));
  end;

To prove the assertion, |GNATprove| will attempt to verify both that ``B (I)``
is true for all ``I`` and that ``C (I)`` can be deduced from ``B (I)``.
After the assertion, the call to ``B`` does not occur in the context anymore,
it is as if the assertion ``(for all I in 1 .. 100 => C (I))`` had been written
directly. Remark that here, ``B`` is really a lemma. Its result does not matter
in itself (it always returns True) but its postcondition gives additional
information for the proof (see the :ref:`SPARK Lemma Library` for more
information about lemmas).

As can be seen in the example above, ``By`` and ``So`` may not necessarily
occur at top-level in an assertion. However, because of their specific
treatment, they are only allowed in specific contexts. We define these
supported contexts in a recursive way:

* As the expression of a ``pragma Assert`` or ``Assert_And_Cut``;

* As an operand of a AND, OR, AND THEN, or OR ELSE operation which itself occurs
  in a supported context;

* As the THEN or ELSE branch of a IF expression which itself occurs in a
  supported context;

* As an alternative of a CASE expression which itself occurs in a supported
  context;

* As the condition of a quantified expression which itself occurs in a supported
  context;

* As a parameter to a call to either ``By`` or ``So`` which itself occurs in a
  supported context;

* As the body expression of a DECLARE expression which itself occurs in a
  supported context.
