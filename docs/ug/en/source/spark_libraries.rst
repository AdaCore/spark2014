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
project file templates :file:`<spark-install>/lib/gnat/sparklib.gpr.templ` (or
through :file:`<spark-install>/lib/gnat/sparklib_light.gpr.templ`
in an environment without units ``Ada.Numerics.Big_Numbers.Big_Integers`` and
``Ada.Numerics.Big_Numbers.Big_Reals``). Header files of the SPARK library are
available through :menuselection:`Help --> SPARK --> SPARKlib` menu item in
GNAT Studio. To use this library in a program, you need to copy the project
template that corresponds to your runtime, remove the ``.templ`` suffix in name and
adapt the project file by providing appropriate values for the object directory (attribute
``Object_Dir`` in the project file) and the list of excluded source files
(attribute ``Excluded_Source_Files`` in the project file). The simplest is just
to provide a value for ``Object_Dir`` and inherit ``Excluded_Source_Files`` from
the parent project:

.. code-block:: gpr

   project SPARKlib extends "sparklib_internal" is
      for Object_Dir use "sparklib_obj";
      for Excluded_Source_Files use SPARKlib_Internal'Excluded_Source_Files;
   end SPARKlib;

Then, add a corresponding dependency in your project file, for example:

.. code-block:: gpr

  with "sparklib";
  project My_Project is
     ...
  end My_Project;

.. index:: GPR_PROJECT_PATH; for SPARK library

You may need to update the environment variable ``GPR_PROJECT_PATH`` for the
lemma library project to be found by GNAT compiler, as described in
:ref:`Installation of GNATprove`.

In addition, it is possible to enable (or disable, if assertions are enabled
by default) assertion levels defined in the |SPARK| library globally for your
project. It can be done by supplying ``Check_Policy`` or ``Assertion_Policy``
pragmas at the project level. They can be stored in a separate file, for
example, a file ``pragmas.adc`` can be created containing the following pragmas:

.. code-block:: ada

   pragma Check_Policy (SPARKlib_Defensive => Check);
   pragma Check_Policy (SPARKlib_Logic => Ignore);

This file should then by referenced in the ``Builder`` section of your project
file:

.. code-block:: gpr

   package Builder is
      for Global_Configuration_Pragmas use "pragmas.adc";
   end Builder;

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

These libraries define representations for big numbers and basic arithmetic
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
numbers. This makes it possible to benefit from precise support on code using them. Note
that the corresponding Ada libraries ``Ada.Numerics.Big_Numbers.Big_Integers``
and ``Ada.Numerics.Big_Numbers.Big_Reals`` will be handled in the same way, but
might be not available under specific runtimes. It is preferable to use the
units from the SPARK library instead, or use
``Ada.Numerics.Big_Numbers.Big_Integers_Ghost``.

.. note::

   Some functionality of the library is not precisely supported. This includes
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

There are 7 functional containers, which are part of the |SPARK| library:

* ``SPARK.Containers.Functional.Infinite_Sequences``
* ``SPARK.Containers.Functional.Maps``
* ``SPARK.Containers.Functional.Multisets``
* ``SPARK.Containers.Functional.Sets``
* ``SPARK.Containers.Functional.Total_Maps``
* ``SPARK.Containers.Functional.Trees``
* ``SPARK.Containers.Functional.Vectors``

Sequences defined in ``Functional.Vectors`` are no more than ordered collections
of elements. In an Ada like manner, the user can choose the range used to index
the elements:


.. code-block:: ada

    function Length (S : Sequence) return Count_Type;
    function Get (S : Sequence; N : Index_Type) return Element_Type;

The sequences defined in ``Functional.Infinite_Sequences`` behave as the ones of
``Functional.Vectors``. The difference between them lies in the fact that the
infinite one is indexed by mathematical integers.

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

Total maps defined in ``Functional.Total_Maps`` are maps in which every key is
mapped to an element. Keys that have not been explicitly set are mapped to a
default element supplied at instantiation. As a result, ``Get`` is a total
function and there is no ``Has_Key`` primitive:

.. code-block:: ada

    function Get (M : Map; K : Key_Type) return Element_Type;
    function Set (M : Map; K : Key_Type; E : Element_Type) return Map;

Multisets are mathematical sets associated with a number of occurrences:

.. code-block:: ada

   function Nb_Occurence (S : Multiset; E : Element_Type) return Big_Natural;
   function Cardinality (S : Multiset) return Big_Natural;

Functional trees are recursive mathematical data structures such that non-empty
trees contain an element and a child tree per element of the ``Way_Type`` formal
parameter type:

.. code-block:: ada

   function Is_Empty (Container : Tree) return Boolean;
   function Get (Container : Tree) return Element_Type;
   function Child (Container : Tree; W : Way_Type) return Tree;

Except for trees, functional container types support quantification over their
elements (or keys for functional maps).

These containers can easily be used to model user defined data structures. They
were used to this end to annotate and verify a package of allocators (see
the ``allocators`` example provided with a SPARK installation). In
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

   Instances of container packages, both functional and formal, are subject
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

.. note::

   Functional sets, maps and multisets operate with a user-provided equivalence
   relation, which might be different from the logical equality. In this case,
   all elements or keys of an equivalence class are removed or included
   together in the container. This can sometimes have surprising results.
   For example, ``Contains`` can return ``True`` if an equivalent (but not
   equal) element has been added to a set. Similarly, the quantified
   expression ``for some E of S => Cond (E)`` might be proved if Cond is
   ``False`` for all elements that were explicitly added to the set,
   but ``True`` for an object equivalent to such an element.

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
:ref:`Annotation for Handling Specially Higher Order Functions`)
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
  ``Ada.Containers.Vectors``. They define containers as
  controlled tagged types, so that memory for the container is automatically
  reallocated during assignment and automatically freed when the container
  object's scope ends.
* The bounded containers not using dynamic allocation, for example
  ``Ada.Containers.Bounded_Vectors``. They define containers as discriminated
  tagged types, so that the memory for the container can be reserved at
  initialization.

Although bounded containers are better suited to critical software development,
neither controlled containers nor bounded containers can be used in |SPARK|,
because their API does not lend itself to adding suitable contracts ensuring
correct usage in client code as per the restrictions of |SPARK| (in particular
:ref:`Absence of Interferences`).

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

The 6 others are unbounded and indefinite, and are controlled:

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
    discriminant. Instead, it is implicitly set to its maximum value. All the
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

Cursors of formal containers do not hold a reference to a specific container,
as this would otherwise introduce aliasing between container and cursor
variables, which is not supported in |SPARK|, see :ref:`Absence of
Interferences`. As a result, the same cursor can be applied to multiple
container objects. The Ada rules which define when a cursor becomes *invalid*,
so that using it leads to erroneous execution, are no longer relevant. Instead,
which cursors remain valid in a container after an operation is specified on
a case-by-case basis on each operation.

As a consequence of this difference, only procedures and functions that take
the container as parameter to query its content are available on formal
containers. For example, the two-parameter ``Has_Element`` function is
available on formal containers while the single-parameter one is not:

.. code-block:: ada

   function Has_Element (Container : T; Position : Cursor) return Boolean;
   --  This function is part of the SPARK library

   function Has_Element (Position : Cursor) return Boolean;
   --  This function is not as the Cursor does not contain a reference to the container

Procedures like ``Update_Element`` or ``Query_Element`` that iterate over a
container are not defined on formal containers, nor are functions returning
iterator objects like ``Iterate``. Instead, formal containers use the
``Iterable`` aspect to allow iteration and quantification over containers, see
:ref:`Quantification over Formal Containers`. As a result, the notion of
tampering checks as defined for standard Ada containers is not relevant on
formal containers.

Functions used to gain read or write access to an individual component of a
container such as ``Reference`` or ``Constant_Reference`` have been adapted to
use the notions of borrowing and observing of the :ref:`Memory Ownership Policy`
of |SPARK|. They are defined as `traversal functions` which return values of
an anonymous access type. The fact that the container is not updated while such
a reference exists is ensured by ownership:

.. code-block:: ada

   function Constant_Reference (Container : aliased T;
                                Position  : Cursor)
     return not null access constant Element_Type
   with Pre => Has_Element (Container, Position);

   function Reference (Container : not null access T;
                       Position  : Cursor)
     return not null access Element_Type
   with Pre => Has_Element (Container.all, Position);

For each container type, the library provides model functions that are used to
annotate subprograms from the API. The different models supply different levels
of abstraction of the container's functionalities. These model functions are
grouped in :ref:`Ghost Packages` named ``Formal_Model``.

The higher level view of a container is usually the mathematical structure of
element it represents. We use a sequence for ordered containers such as lists
and vectors and a mathematical map for imperative maps. This allows us to
specify the effects of a subprogram in a very high level way, not having to
consider cursors nor order of elements in a map:

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


Switching between the different levels of model functions makes it possible to express
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

Assertion Levels in the SPARK Library
-------------------------------------

The |SPARK| library introduces several :ref:`Assertion Levels` that are used in
particular in the container libraries. These levels are available in all
projects that use the |SPARK| library.

The assertion level ``SPARKlib_Defensive`` allows enabling preconditions
on container operations. It is useful in particular if these operations are
called from non-proved code. The assertion level ``SPARKlib_Logic`` is for
models of formal containers. It can be enabled in the full runtime. It is
also used for the ghost versions of the :ref:`Big Numbers Library` and
:ref:`Functional Containers Library`, but, as these libraries require
finalization, it cannot be enabled in the light runtime.

Finally, some features of the container library (both functional and formal)
might not have executable semantics. To ensure that user code never attempts to
execute them, these subprograms are associated with the assertion level
``SPARKlib_Full`` that depends on ``Static`` and can never be enabled at
runtime. These non-executable features include quantified expressions over
functional maps, sets, and multisets and logical equality in functional and
formal containers.

The assertion level ``SPARKlib_Full`` is also used for postconditions
on container operations, as it is never useful to execute them.

Quantified Expressions over Functional Maps, Sets, and Multisets
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Functional maps, sets, and multisets take as parameters an equivalence relation.
Inclusion in the container works modulo equivalence: when ``Add`` or ``Remove``
is called, the whole equivalence class is included or excluded at once. As
equivalence classes might be infinite, quantified expressions over elements of
a set or multiset or keys of a map could fail to terminate.

To replace quantified expressions over a functional map, set, or multiset
occurring in
the code, it is possible to use a loop over the ``Iterable_Map``,
``Iterable_Set``, or ``Iterable_Multiset`` types instead. They use the
``Choose`` function to get an unspecified element of the container from a
different equivalence class at each iteration of the loop. As an example:

.. code-block:: ada

  B := (for some E of S => P (E));

can be replaced by:

.. code-block:: ada

  B := False;
  for C in Iterate (S) loop
     pragma Loop_Invariant (for all E of S => (if not Contains (C, E) then not P (E)));
     if P (Choose (C)) then
        B := True;
        exit;
     end if;
  end loop;

Logical Equality
^^^^^^^^^^^^^^^^

The specifications of most formal and functional containers use
`logical equality` to specify that all properties of elements placed in the
container are preserved (see
:ref:`Annotation for Accessing the Logical Equality for a Type`).
Using logical equality to express such properties increases provability of user
code, as it is optimally precise and
natively handled by the automated solvers in the background of SPARK.
However, logical equality does not always correspond to Ada equality, and there
are even types for which it is not possible to write a valid logical equality in
Ada, due to how things are encoded in the backend of the tool.
As a result, logical equality functions used in the specification of formal and
functional containers are not executable.

For formal containers, as the logical equality is given as a parameter to the
functional containers used as models, the models themselves are not executable.
As a result, it is not possible to execute ghost code or assertions that mention
these model functions.

.. index:: pointers

Pointers Library
----------------

The ownership policy of |SPARK| (see :ref:`Memory Ownership Policy`) makes it
possible to verify programs using pointers without reasoning about aliasing.
In general, this allows |GNATprove| to verify pointer-based programs in a
scalable way, with few user-supplied annotations. However, in some cases, the
ownership policy may be considered too constraining. In particular, it does
not permit data structures in which a memory cell is designated by several
pointers, like doubly linked lists or graphs, and it restricts the places where
pointers can be moved. The pointer library, which is part of the |SPARK|
library (see :ref:`SPARK Library`), provides generic units lifting these
restrictions while still allowing |GNATprove| to verify their usage. Programs
which do not need them should use regular access types.

There are 5 generic units providing pointers with aliasing:

* ``SPARK.Pointers.Explicit_Reclamation.Global_Memory``
* ``SPARK.Pointers.Explicit_Reclamation.Separate_Memory``
* ``SPARK.Pointers.Auto_Reclaimed.Immutable``
* ``SPARK.Pointers.Auto_Reclaimed.Global_Memory``
* ``SPARK.Pointers.Auto_Reclaimed.Separate_Memory``

Units in ``Explicit_Reclamation`` model the memory explicitly as a map from
pointers to designated values. A memory cell stays valid until it is
deallocated by a call to ``Dealloc``. Units in ``Auto_Reclaimed`` use
reference counting: a memory cell is reclaimed automatically when the last
pointer designating it disappears, and reclamation does not appear in the
model. As reference counting does not reclaim cycles, cyclic structures should
use weak handles (see below). In ``Auto_Reclaimed.Immutable``, the designated
data cannot be modified, so a pointer can be considered as the value it
designates and there is no memory to reason about.

Units named ``Global_Memory`` use a single memory for all the pointers of an
instance. Units named ``Separate_Memory`` split the memory into objects of type
``Memory_Type``, typically one per data structure. Memory cells can be moved
from one memory object to another using ``Move_Memory``. As memory objects are
subject to ownership, they are necessarily disjoint, so modifying a data
structure is known to preserve the others. With a global memory, contracts are
simpler, but this preservation must be proved by the user. In
``Explicit_Reclamation.Separate_Memory``, a memory object which is not empty at
the end of its scope is reported as a memory leak.

The following table summarizes the main differences between these units:

.. csv-table::
   :header: "Unit", "Reclamation", "Designated data", "Memory"
   :widths: 3, 2, 1, 2

   "``Explicit_Reclamation.Global_Memory``", "``Dealloc``", "mutable", "one global memory"
   "``Explicit_Reclamation.Separate_Memory``", "``Dealloc``, leaks detected", "mutable", "memory objects"
   "``Auto_Reclaimed.Immutable``", "automatic", "immutable", "none"
   "``Auto_Reclaimed.Global_Memory``", "automatic", "mutable", "one global memory"
   "``Auto_Reclaimed.Separate_Memory``", "automatic", "mutable", "memory objects"

Pointers with aliasing cannot be used directly as components of their
designated type, as a generic cannot be instantiated with an incomplete type.
To build recursive data structures, the designated type can instead contain
handles, declared in one of the following units, and converted to and from
pointers by the ``Handle_Operations`` package nested in each unit above:

* ``SPARK.Pointers.Handles.Plain_Handles``
* ``SPARK.Pointers.Handles.Owning_Handles``
* ``SPARK.Pointers.Handles.Auto_Reclaimed_Handles``

Handles of ``Auto_Reclaimed_Handles`` can be weak, that is, not counted as
references. They should be used to break cycles.

Other restrictions of the ownership policy concern the places where a pointer
can be moved. Some are language restrictions, intended to make verification
simpler. For example, an ``in out`` parameter or a global variable cannot be
left moved on subprogram return. Others are tool limitations. For
example, the borrow checker is imprecise on arrays, and does not know which
component has been moved. These restrictions can be lifted using poisoned
pointers, which can represent a value that has been moved out of and cannot be
read, so that |GNATprove| can reason about partially moved structures. There
are 2 generic units providing them:

* ``SPARK.Pointers.Poisoned.Views`` can be used to lift the restrictions
  locally. It provides a view of an existing object, subject to ownership,
  through traversal functions.
* ``SPARK.Pointers.Poisoned.Pointers`` defines a new pointer type, so that the
  restrictions are lifted for all objects of the type.

Finally, the ``SPARK.Pointers.Abstract_Maps``, ``SPARK.Pointers.Abstract_Sets``
and ``SPARK.Pointers.Abstract_Reachability`` units provide helpers to write
the models and contracts of data structures built using the pointer library.

Units instantiating one of the ``Auto_Reclaimed`` generics should enable GNAT
extensions using ``pragma Extensions_Allowed (On)``. In the light runtime, the
``Handle_Operations`` generic packages of these units can only be instantiated
at library level, as they take the ``'Access`` attribute of a subprogram
declared in their private part.

Pointers with Explicit Reclamation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The units ``SPARK.Pointers.Explicit_Reclamation.Global_Memory`` and
``SPARK.Pointers.Explicit_Reclamation.Separate_Memory`` provide pointers with
aliasing whose designated memory cells are deallocated by the user. They are
generic in the type ``Object`` of the designated values, which can be
indefinite and might be subject to ownership, and in a ghost function
``Is_Reclaimed``:

.. code-block:: ada

   generic
      type Object (<>) is private;
      with function Is_Reclaimed (X : Object) return Boolean
        with Ghost => Static;

The function ``Is_Reclaimed`` should only return True on values which do not
own any memory. It is used to ensure that no memory is leaked when a memory
cell is deallocated or overwritten. If ``Object`` is not subject to ownership,
it can always return True.

The type ``Pointer`` is not subject to ownership: copying a pointer creates an
alias. Pointers are initialized to ``Null_Pointer`` by default and their
equality is the logical equality. The memory is modelled as a ``Memory_Map``, a
map from pointers to values of type ``Object``. Function
``In_Memory`` returns whether the memory holds a cell for a given pointer, and
function ``Get`` gives access to its value:

.. code-block:: ada

   function In_Memory (M : Memory_Map; P : Pointer) return Boolean;
   function Get
     (M : Memory_Map; P : Pointer) return not null access constant Object;

Pointers can only be dereferenced if they designate a cell of the memory,
which ensures that dangling pointers are never dereferenced. The contracts of
the operations use three ghost functions to describe how the memory is
modified, in terms of footprints, which are sets of pointers:

* ``Allocates (M1, M2, Target)`` states that the cells of ``M2`` which are
  not in ``M1`` are exactly the ones designated by ``Target``;

* ``Deallocates (M1, M2, Target)`` states that the cells of ``M1`` which are
  not in ``M2`` are exactly the ones designated by ``Target``;

* ``Writes (M1, M2, Target)`` states that cells which are both in ``M1`` and
  ``M2`` and are not designated by ``Target`` are unchanged.

The functions ``None`` and ``Only (P)`` return the empty footprint and the
footprint containing only ``P``. These functions can also be used in the
contracts of user subprograms. As an example, here is the contract of the
procedure ``Dealloc`` of ``Global_Memory``, which deallocates the cell
designated by ``P`` if ``P`` is not null, and resets ``P`` to
``Null_Pointer``:

.. code-block:: ada

   procedure Dealloc (P : in out Pointer)
   with
     Global  => (In_Out => Memory),
     Pre     =>
       P = Null_Pointer
       or else
         (In_Memory (Model (Memory), P)
          and then Is_Reclaimed (Get (Model (Memory), P).all)),
     Post    =>
       P = Null_Pointer
       and then Allocates (Model (Memory)'Old, Model (Memory), None)
       and then
         (if P'Old = Null_Pointer
          then Deallocates (Model (Memory)'Old, Model (Memory), None)
          else Deallocates (Model (Memory)'Old, Model (Memory), Only (P'Old)))
       and then Writes (Model (Memory)'Old, Model (Memory), None);

Cells are allocated by instances of the generic procedure ``Create``, which
builds the designated value from an input using the ``Create_Object``
function. The generic package ``Copy_Operations`` provides operations which
copy the designated value using its ``Copy`` function: ``Create_Copy``
allocates a cell holding a copy of its object parameter, ``Deref`` returns a
copy of the designated value, and ``Assign`` replaces it by a copy of its
object parameter:

.. code-block:: ada

   generic
      type Input (<>) is private;
      with function Create_Object (X : Input) return Object;
   procedure Create (X : Input; P : out Pointer);

   generic
      with function Copy (O : Object) return Object;
   package Copy_Operations is
      procedure Create_Copy (O : Object; P : out Pointer);
      function Deref (P : Pointer) return Object;
      procedure Assign (P : Pointer; O : Object);
   end Copy_Operations;

The designated value can also be accessed in place, without copies, using the
traversal functions ``Constant_Reference`` and ``Reference``, which observe or
borrow the memory:

.. code-block:: ada

   function Constant_Reference
     (Memory : Memory_Type; P : Pointer) return not null access constant Object;
   function Reference
     (Memory : Memory_Type; P : Pointer) return not null access Object;

In ``Global_Memory``, all the cells are stored in a single object ``Memory``,
declared in the instance and initially empty. It is used as a global variable
by all the operations, except ``Constant_Reference`` and ``Reference`` which
take it as a parameter, so users do not need to declare memory objects. The
model of the memory is given by the function ``Model``. Reclamation is not
checked: no leak is reported when a cell is no longer reachable, or even when
the instance goes out of scope.

In ``Separate_Memory``, memory objects of type ``Memory_Type`` are declared by
the user and passed as parameters to all the operations. The model of a memory
object is given by the function ``"+"``. As memory objects are subject to
ownership, they are necessarily disjoint, so an operation can only modify the
memory it is given. Cells can be moved from one memory object to another
using ``Move_Memory``:

.. code-block:: ada

   procedure Move_Memory (Source, Target : in out Memory_Type; F : Footprint);

A memory object which is not empty when it goes out of scope is reported as a
memory leak.

In both units, the nested package ``Handle_Operations`` provides conversions
between pointers and plain handles, to build recursive data structures (see
below).

As an example, the following package instantiates ``Global_Memory`` for
integers:

.. literalinclude:: /examples/ug__pointers_explicit_reclamation/int_pointers.ads
   :language: ada
   :linenos:

In the procedure ``Aliasing`` below, ``X`` and ``Y`` designate the same memory
cell. Modifying the cell through ``X`` modifies the value designated by
``Y``, and after the cell is deallocated through ``X``, ``Y`` can no longer be
dereferenced:

.. literalinclude:: /examples/ug__pointers_explicit_reclamation/aliasing.adb
   :language: ada
   :linenos:

|GNATprove| proves all the checks of ``Aliasing``:

.. literalinclude:: /examples/ug__pointers_explicit_reclamation/test.out
   :language: none

Auto-Reclaimed Pointers
^^^^^^^^^^^^^^^^^^^^^^^

The units ``SPARK.Pointers.Auto_Reclaimed.Immutable``,
``SPARK.Pointers.Auto_Reclaimed.Global_Memory`` and
``SPARK.Pointers.Auto_Reclaimed.Separate_Memory`` provide pointers with
aliasing whose designated memory cells are reclaimed automatically. They are
generic in the type ``Object`` of the designated values, which can be
indefinite and might be subject to ownership, and in a procedure ``Reclaim``:

.. code-block:: ada

   generic
      type Object (<>) is private;
      with procedure Reclaim (X : in out Object) is null;

The procedure ``Reclaim`` should reclaim all the memory owned by its
parameter. If ``Object`` is not subject to ownership, the default null
procedure can be used. The designated values are reference counted: a memory
cell is reclaimed, calling ``Reclaim`` on its value, when the last pointer
designating it disappears. Reclamation does not appear in the model, so no
memory leak is ever reported. However, reference counting does not reclaim
cycles. For a cyclic data structure to be reclaimed, one edge of each cycle
should use a weak handle (see below). This is not verified by |GNATprove|.

.. note::

   Modelling the memory as if reclamation never happened is sound, even though
   cells are physically reclaimed. A cell is only reclaimed once the last pointer
   designating it disappears, so by construction no pointer to a reclaimed cell is
   ever left in the program. As executable code can only reach a cell through a
   pointer that designates it, a reclaimed cell can never be dereferenced, and the
   model's claim that the cell is still there can never be observed to be wrong.

In ``Immutable``, the designated values cannot be modified. As a result, there
is no memory to reason about: a pointer is modelled by the value it designates,
and two pointers designating equal values are logically equal. Pointers can
only be compared to ``Null_Pointer`` using ``"="``. Pointers are created by
instances of the generic function ``Create``, or by ``Create_Copy`` in the
generic package ``Copy_Operations``. The designated value can be copied
using ``Deref``, or accessed in place using ``Constant_Reference``:

.. code-block:: ada

   generic
      type Input (<>) is private;
      with function Create_Object (X : Input) return Object;
   function Create (X : Input) return Pointer;

   generic
      with function Copy (O : Object) return Object;
   package Copy_Operations is
      function Create_Copy (O : Object) return Pointer;
      function Deref (P : Pointer) return Object;
   end Copy_Operations;

   function Constant_Reference
     (P : Pointer) return not null access constant Object;

.. note::

   ``Auto_Reclaimed.Immutable`` can be used in place of an access-to-constant
   type whose designated data is dynamically allocated and should later be
   reclaimed. As of now, |SPARK| provides no way to reclaim the memory designated
   by an access-to-constant type, so such allocations leak. ``Immutable`` offers
   the same guarantee that the designated value cannot be modified, while
   reclaiming the memory automatically through reference counting.

The units ``Auto_Reclaimed.Global_Memory`` and
``Auto_Reclaimed.Separate_Memory`` have the same model and API as their
counterparts in ``Explicit_Reclamation`` (see :ref:`Pointers with Explicit
Reclamation`), except that there is no ``Dealloc`` procedure, and cells never
disappear from the model. As a consequence, a memory object of
``Separate_Memory`` which is not empty when it goes out of scope is not
reported as a leak. In ``Global_Memory``, the memory is an abstract state,
whose model is given by the function ``Model``.

.. note::

   In ``Global_Memory`` the memory only ever grows: reclamation is invisible in
   the model, so a cell never leaves it (this is captured by
   ``Monotonous_Memory``). By construction, any pointer that has been created
   therefore stays in the memory: every non-null ``Pointer`` value satisfies
   ``In_Memory (Model, P)`` for the rest of the program. |GNATprove| cannot track
   this by itself, however -- the ``In_Memory`` precondition of operations such as
   ``Assign`` and ``Deref`` must still be discharged at each call. A client that
   relies on the property therefore has to thread it through its own contracts:
   requiring ``In_Memory (Model, P)`` where a pointer is used, ensuring it where
   one is created, and propagating ``Monotonous_Memory (Model'Old, Model)`` across
   operations that modify the memory, as the library operations do.

In all three units, the generic package ``Handle_Operations`` provides
conversions between pointers and auto-reclaimed handles, to build recursive
data structures (see below).

As an example, the following package instantiates ``Global_Memory`` for
integers:

.. literalinclude:: /examples/ug__pointers_auto_reclaimed/int_pointers.ads
   :language: ada
   :linenos:

As in the example of ``Explicit_Reclamation``, ``X`` and ``Y`` designate the
same memory cell in the procedure ``Aliasing`` below, so modifying the cell
through ``X`` modifies the value designated by ``Y``. There is no need to
deallocate the cell, which is reclaimed when ``X`` and ``Y`` go out of scope:

.. literalinclude:: /examples/ug__pointers_auto_reclaimed/aliasing.adb
   :language: ada
   :linenos:

|GNATprove| proves all the checks of ``Aliasing``:

.. literalinclude:: /examples/ug__pointers_auto_reclaimed/test.out
   :language: none

Poisoned Pointers
^^^^^^^^^^^^^^^^^

The units ``SPARK.Pointers.Poisoned.Views`` and
``SPARK.Pointers.Poisoned.Pointers`` lift restrictions on moves of the
ownership policy of |SPARK| (see :ref:`Pointers Library`). Instead of
rejecting a move, they represent the value that has been moved out of as
poisoned: it cannot be read, but it is part of the model. As a result, a
partially moved object is an ordinary value, which can be passed as a
parameter, returned from a subprogram, and described in contracts. |GNATprove|
verifies, by proof rather than by the borrow checker, that poisoned values are
never read.

Both units are generic in the type ``Object`` of the values, which might be
subject to ownership, and in a ghost function ``Is_Reclaimed``, as the units of
``Explicit_Reclamation`` (see :ref:`Pointers with Explicit Reclamation`). The
ghost function ``Is_Poisoned`` returns whether a value is poisoned, and
``Peek`` gives the value of a value which is not. The subtypes
``Readable_View`` and ``Readable_Pointer`` only contain values which are not
poisoned. Values of both units are subject to ownership and need reclamation:
at the end of its scope, a value should either be poisoned or hold a
reclaimed value. The procedure ``Move`` moves a value from its source to its
target, which should be reclaimed, and the function ``Take`` returns the value
of its parameter. Both leave the source poisoned:

.. code-block:: ada

   function Take (Source : in out View) return View;
   procedure Move (Source : in out View; Target : in out View);

Values which are not poisoned can be accessed in place using the traversal
functions ``Constant_Reference`` and ``Reference``. The generic package
``Array_Operations`` provides moves of elements and slices of arrays. As the
source and the target of ``Move`` are both ``in out`` parameters, it cannot be
used to move an element inside a single array. The procedure ``Relocate`` can be
used instead:

.. code-block:: ada

   procedure Relocate
     (A : in out View_Array; Source : Index_Type; Target : Index_Type);

The unit ``Poisoned.Views`` lifts the restrictions locally, on an existing
object or array, which should be definite. The function ``Get_View`` borrows it
as a readable view:

.. code-block:: ada

   function Get_View
     (X : aliased in out Object) return not null access Readable_View;

The view should be readable again when the borrow ends. As the subtype
predicate of ``Readable_View`` is checked after each call, the view can only be
broken temporarily inside a subprogram with a formal parameter of type
``View``, which should restore it before returning. Instances of the generic
function ``Create`` build views of new values. They can be used to fill a
poisoned view, or to build local views which do not correspond to an existing
object.
Versions of ``Take`` and ``Move`` move the value of a view out to an object,
for example to insert it into another data structure:

.. code-block:: ada

   function Take (Source : in out View) return Object;
   procedure Move (Source : in out View; Target : in out Object);

There are no moves in the other direction, as the source object would still
own its value. Views of new values are built using ``Create`` instead.

The unit ``Poisoned.Pointers`` lifts the restrictions for all the objects of a
type. It defines a new type ``Pointer`` of owning pointers, whose designated
type can be indefinite. The null pointer ``Null_Pointer`` is never poisoned.
Pointers are created by instances of the generic function ``Create`` and
deallocated using the procedure ``Reclaim``. The generic package
``Copy_Operations`` provides the functions ``Create_Copy`` and ``Deref``, and
the procedure ``Assign``, which copy the designated value using its ``Copy``
function. The package ``Handle_Operations`` provides conversions between
pointers and owning handles, to build recursive data structures (see below).

As an example, consider a procedure ``Replace`` which replaces the element at
index ``I`` of an array ``A`` of access values by a new value, and returns the
element which has been moved out in ``Old``. Written with regular access
types, by moving ``A (I)`` to ``Old`` and assigning a new value to ``A (I)``,
it is rejected by |GNATprove|: the borrow checker does not know which component
of ``A`` is designated by ``I``, so assigning ``A (I)`` does not restore the
component which has been moved out of ``A``. It can be written using
``Poisoned.Views`` instead. The following package instantiates
``Poisoned.Views`` for the access type, as well as its ``Array_Operations``
package and its ``Create`` function:

.. literalinclude:: /examples/ug__pointers_poisoned/acc_views.ads
   :language: ada
   :linenos:

The procedure ``Replace`` below takes the view of the array ``A``. The moves
are done in the procedure ``Replace_In_View``, whose parameter is of type
``View_Array``, so that the view is readable again when the borrow ends:

.. literalinclude:: /examples/ug__pointers_poisoned/replacing.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__pointers_poisoned/replacing.adb
   :language: ada
   :linenos:

|GNATprove| proves all the checks of ``Replacing``:

.. literalinclude:: /examples/ug__pointers_poisoned/test.out
   :language: none

Handles
^^^^^^^

The designated type of a pointer unit must be complete when the unit is
instantiated, so it cannot contain a component of the ``Pointer`` type of the
instance. To build recursive data structures, the designated type can instead
contain handles, declared before the instantiation. The package
``Handle_Operations`` of the instance provides conversions between handles
and pointers. The ghost function ``Valid_Handle`` states that a handle was
obtained from a pointer of the instance. It is the precondition of the
conversions from handles to pointers. Equality on handles is abstract.
Handles should be compared using the ``"="`` function of
``Handle_Operations``, when there is one. Handles are not initialized by
default: a handle which does not designate anything can be obtained by
converting ``Null_Pointer``.

There are 3 units defining handles, each corresponding to a kind of pointer
units:

* ``SPARK.Pointers.Handles.Plain_Handles`` is used by the units of
  ``Explicit_Reclamation``. The package ``Handle_Operations`` is a nested
  package of the instance, providing the conversion functions ``To_Handle``
  and ``Of_Handle``.

* ``SPARK.Pointers.Handles.Owning_Handles`` is used by
  ``Poisoned.Pointers``. Handles are subject to ownership and should be
  reclaimed. The package ``Handle_Operations`` is a nested package of the
  instance. It provides the traversal functions ``Constant_Reference`` and
  ``Reference`` to access the pointer designated by a handle in place, which
  requires handle components to be ``aliased``, and the generic function
  ``Create_Handle`` to create a new handle.

* ``SPARK.Pointers.Handles.Auto_Reclaimed_Handles`` is used by the units of
  ``Auto_Reclaimed``. It provides two generic packages,
  ``Without_Weak_Handles`` for ``Auto_Reclaimed.Immutable`` and
  ``With_Weak_Handles`` for ``Auto_Reclaimed.Global_Memory`` and
  ``Auto_Reclaimed.Separate_Memory``. The package ``Handle_Operations`` is a
  generic package taking an instance of one of them as a parameter. The two
  instances should have the same accessibility level.

In ``With_Weak_Handles``, handles can be strong or weak. Strong handles are
counted as references to the designated cell, but weak handles are not. As a
result, weak handles can be used to break cycles in data structures, like the
back pointers of a doubly linked list, so that they can be reclaimed
automatically (see :ref:`Auto-Reclaimed Pointers`). As the cell designated by
a weak handle might have been reclaimed, converting it back to a pointer or to
a strong handle using ``Of_Weak_Handle`` or ``To_Strong_Handle`` might fail.
In this case, these functions return ``Null_Pointer``. They are volatile
functions, as reclamation is not part of the model. The generic package
``Witnessed_Conversions`` provides deterministic versions of these functions,
which cannot fail, by taking as a parameter a ``Witness`` function returning
the pointer designated by the handle. This function is never called: being
able to provide it shows that the designated cell is still alive.

In ``Auto_Reclaimed.Immutable``, the package ``Handle_Operations`` also
provides the generic packages ``Structural_Variant`` and
``Multiway_Structural_Variant``. They are instantiated with a function
``Next`` returning the handle components of a cell, and provide a ghost
function ``Weight`` which decreases along the structure. It can be used in
subprogram variants to prove the termination of recursive subprograms
traversing the structure. It is correct because immutable structures cannot
contain cycles.

As an example, the following package instantiates ``Immutable`` for list
cells containing a handle designating the next cell of the list, together
with ``Structural_Variant``:

.. literalinclude:: /examples/ug__pointers_handles/list_pointers.ads
   :language: ada
   :linenos:

The package ``Int_Lists`` below uses these instances to define immutable
lists of integers. The ghost function ``Valid_List`` states that all the
handles of a list are valid. Its termination, and the termination of the
function ``Contains``, are proved using the ``Weight`` function of
``Structural_Variant``:

.. literalinclude:: /examples/ug__pointers_handles/int_lists.ads
   :language: ada
   :linenos:

|GNATprove| proves all the checks of ``Int_Lists``, including the subprogram
variants of ``Valid_List`` and ``Contains``:

.. literalinclude:: /examples/ug__pointers_handles/test.out
   :language: none

Model Helpers
^^^^^^^^^^^^^

The units ``SPARK.Pointers.Abstract_Maps`` and ``SPARK.Pointers.Abstract_Sets``
define the maps and sets used in the models of the pointer library, like the
memory maps and the footprints. Their types are null records, so they take no
memory space and can be used in objects and parameters which cannot be ghost,
like the memory objects. Only their constructors are executable, and they do
nothing at run time. The functions querying their content are ghost and not
executable. Abstract sets can also be constructed by comprehension: the
function ``Elements`` returns the set of all the elements for which a given
function returns True. Such a set might not be finite.

The unit ``SPARK.Pointers.Abstract_Reachability`` is the counterpart of the
``SPARK.Higher_Order.Reachability`` package (see
:ref:`Linked Structures in Arrays`) for linked structures stored in an abstract
map. It provides the
same functions and lemmas. Its generic parameters are an instance of
``Abstract_Maps``, the equality on keys, and a ghost function ``Next``
returning the key of the next cell. Its formal set and sequence packages are
ghost, so they should be instantiated in a ghost package.

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
the final executable without assertions (when switch ``-gnata`` is not set). On
the contrary, when compiling with assertions for testing (when switch ``-gnata``
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

Currently, the SPARK lemma library provides the following lemmas:

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
  the user for their specific fixed-point type.

* Lemmas on floating point arithmetic in file
  ``spark-lemmas-floating_point_arithmetic.ads``, that are instantiated for
  single-precision floats (``Float``) in file
  ``spark-lemmas-float_arithmetic.ads`` and for double-precision floats
  (``Long_Float``) in file ``spark-lemmas-long_float_arithmetic.ads``.

* Lemmas on unconstrained arrays in file
  ``spark-lemmas-unconstrained_array.ads``, that need to be instantiated by the
  user for their specific type of index and element, and specific ordering
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
(see :ref:`SPARK Library`). Higher order functions over functional containers
are provided in child packages of the functional containers instead (see
:ref:`Functional Containers Library`).

This library consists of a set of generic entities defining usual operations on
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

      with function Init_Prop (A : Element_In) return Boolean with Ghost;
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
     (X < Integer'Last)
   with Ghost;

   function Increment_One (X : Natural) return Natural is (X + 1) with
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

.. note::

   Unlike the :ref:`SPARK Lemma Library`, this library cannot be verified once
   and for all, as its correctness depends on the actual parameters of each
   instance. Each instance should be verified with |GNATprove|. This includes
   the ghost procedures documented as axioms, which state properties that the
   actual parameters should have (see :ref:`Fold Functions` for an example).

Map Functions
^^^^^^^^^^^^^

The ``Map`` function presented above is declared in file
``spark-higher_order.ads``, together with three variants:

* ``Map_I`` takes a function ``F`` with an additional parameter for the index
  of the element in the array. ``Init_Prop`` also takes this index as a
  parameter.

* ``Map_Proc`` modifies an array in place instead of returning a new array.
  The type of the elements is therefore the same before and after the
  application of ``F``.

* ``Map_I_Proc`` modifies an array in place and passes the index of the element
  to ``F`` and ``Init_Prop``.

As an example, here is the declaration of ``Map_Proc``:

.. code-block:: ada

   generic
      type Index_Type is range <>;
      type Element is private;
      type Array_Type is array (Index_Type range <>) of Element;

      with function Init_Prop (A : Element) return Boolean with Ghost;
      --  Potential additional constraint on values of the array to allow Map

      with function F (X : Element) return Element;
      --  Function that should be applied to elements of Array_Type

   procedure Map_Proc (A : in out Array_Type) with
     Pre  => (for all I in A'Range => Init_Prop (A (I))),
     Post => (for all I in A'Range => A (I) = F (A'Old (I)));

Fold Functions
^^^^^^^^^^^^^^

Fold functions over unconstrained one-dimensional arrays are defined in file
``spark-higher_order-fold.ads``. They are declared as functions ``Fold`` inside
generic packages. The function ``Fold`` of package ``Fold_Left`` takes as
parameters an array ``A`` and an initial value ``Init`` and applies ``F``
repeatedly to the elements of ``A`` from left to right, starting from ``Init``.
On an array indexed from 1 to 3, it computes
``F (A (3), F (A (2), F (A (1), Init)))``. Package ``Fold_Right`` provides the
same function going from right to left, and packages ``Fold_Left_I`` and
``Fold_Right_I`` provide variants where ``F`` also takes the index of the
element as a parameter.

Here is the declaration of ``Fold_Left``, without the postcondition of
``Fold``:

.. code-block:: ada

   generic
      type Index_Type is range <>;
      type Element_In is private;
      type Array_Type is array (Index_Type range <>) of Element_In;
      type Element_Out is private;

      with function Ind_Prop
        (A : Array_Type; X : Element_Out; I : Index_Type) return Boolean
      with Ghost;
      --  Potential inductive property that should be maintained during fold

      with function Final_Prop (A : Array_Type; X : Element_Out) return Boolean
      with Ghost;
      --  Potential inductive property at the last iteration

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_Left is

      function Fold (A : Array_Type; Init : Element_Out) return Element_Out
      with
        Pre => A'Length = 0 or else Ind_Prop (A, Init, A'First);

   end Fold_Left;

The two ghost functions ``Ind_Prop`` and ``Final_Prop`` are used to describe
the intermediate values of the fold. ``Ind_Prop (A, X, I)`` should hold when
``X`` is the value accumulated before processing the element at index ``I``. It
can be used to show that the precondition of ``F`` is respected, for example to
rule out overflows. ``Final_Prop (A, X)`` should hold when ``X`` is the final
result. It can be used to state properties of the result of the fold. The
precondition of ``Fold`` requires ``Ind_Prop`` to hold for ``Init`` on the
first index of the array, if any. The instance of ``Fold_Left`` then contains
two ghost procedures ``Prove_Ind`` and ``Prove_Last`` which state respectively
that applying ``F`` preserves ``Ind_Prop`` and that applying ``F`` on the last
element establishes ``Final_Prop``:

.. code-block:: ada

   procedure Prove_Ind (A : Array_Type; X : Element_Out; I : Index_Type)
   with
     Ghost,
     Pre  => I in A'Range and then Ind_Prop (A, X, I) and then I /= A'Last,
     Post => Ind_Prop (A, F (A (I), X), I + 1);
   --  Axiom: Ind_Prop should be preserved when going to next index

   procedure Prove_Last (A : Array_Type; X : Element_Out)
   with
     Ghost,
     Pre  => A'Length > 0 and then Ind_Prop (A, X, A'Last),
     Post => Final_Prop (A, F (A (A'Last), X));
   --  Axiom: Final_Prop should be provable at the last iteration from
   --  Ind_Prop.

These procedures have null bodies, which are verified when the instance is
analyzed. If no such properties are needed, ``Ind_Prop`` and ``Final_Prop`` can
be instantiated with functions which always return ``True``.

Packages ``Fold_Left``, ``Fold_Right``, ``Fold_Left_I``, and ``Fold_Right_I``
are defined using auxiliary packages with the ``_Acc`` suffix, which compute
the array of all intermediate values of the fold. They are only used to define
and verify the fold functions and should not be used directly.

As an example, here is how ``Fold_Left`` can be used to compute the maximal
element of an array of integers:

.. literalinclude:: /examples/ug__higher_order_fold/array_max.ads
   :language: ada
   :linenos:

``Max_Prefix (A, X, I)`` states that ``X`` is greater than or equal to all
the elements of ``A`` before index ``I``. It trivially holds for
``Integer'First`` on the first index of ``A``, as there are no elements before
it. |GNATprove| verifies that applying ``Max`` preserves ``Max_Prefix`` and
that it establishes ``Max_All`` on the last element of the array, which is
enough to prove the postcondition of ``Max_Element``.

Fold functions are also provided for two-dimensional arrays in packages
``Fold_2``. They traverse the array row by row, from left to right and from
top to bottom. ``Ind_Prop`` then takes as parameters both the row and the
column of the next element. Two ghost procedures ``Prove_Ind_Col`` and
``Prove_Ind_Row`` state that ``Ind_Prop`` is preserved when going to the next
column and to the next row respectively.

Sum and Count
^^^^^^^^^^^^^

For ease of use, the fold functions are instantiated in
``spark-higher_order-fold.ads`` for the most common cases. Packages ``Sum`` and
``Sum_2`` compute the sum of all the elements of a one-dimensional or a
two-dimensional array, and ``Count`` and ``Count_2`` the number of elements
with a given ``Choose`` property. These functions are defined recursively, so
reasoning about them generally requires induction. To avoid it, these packages
also provide ghost procedures, or lemmas, which state their most useful
properties.

The generic package ``Count`` takes as parameters an array type and a function
``Choose`` on its elements. It provides a function ``Count`` returning the
number of elements of an array for which ``Choose`` returns ``True``, as well as
the following lemmas:

* ``Update_Count`` states how the result of ``Count`` changes when a single
  element of the array is modified.

* ``Count_Zero`` states that ``Count`` returns 0 if and only if ``Choose``
  returns ``False`` on all the elements of the array.

* ``Count_Length`` states that ``Count`` returns the length of the array if
  and only if ``Choose`` returns ``True`` on all the elements of the array.

As an example, here is a procedure that sets an element of an array of integers
to zero, with a postcondition stating how the number of zeros in the array is
affected:

.. literalinclude:: /examples/ug__higher_order_sum_count/count_zeros.ads
   :language: ada
   :linenos:

To verify this postcondition, a copy of the array before the modification is
saved in a ghost constant ``Old`` and the lemma ``Update_Count`` is called after
the modification:

.. literalinclude:: /examples/ug__higher_order_sum_count/count_zeros.adb
   :language: ada
   :linenos:

The generic package ``Sum`` takes as parameters an array type, a type
``Element_Out`` for the result, and a function ``Value`` computing the value of
each element of the array as an ``Element_Out``. ``Element_Out`` is a private
type so that the package can be instantiated both with integer types and with
big integers. As a result, the addition ``Add`` on ``Element_Out`` and its
neutral element ``Zero`` are also provided at instantiation, along with two
ghost functions to express the absence of overflows: ``To_Big`` converts an
``Element_Out`` into a big integer, and ``In_Range`` returns ``True`` on big
integers which can be represented in ``Element_Out``.

The package provides a function ``Sum`` whose precondition ``No_Overflows``
ensures that no intermediate result of the summation overflows. Its
postcondition relates its result to the sum on big integers
``Big_Integer_Sum.Sum``. The ghost package ``Big_Integer_Sum`` also provides the
following lemmas:

* ``Update_Sum`` states how the sum changes when a single element of the array
  is modified.

* ``Sum_Cst`` gives the value of the sum on an array whose elements all have
  the same value.

Here is an instance of ``Sum`` which computes the sum of the elements of an
array of integers:

.. literalinclude:: /examples/ug__higher_order_sum_count/sum_ints.ads
   :language: ada
   :linenos:

Packages ``Sum_2`` and ``Count_2`` provide the same functions and lemmas on
two-dimensional arrays.

Linked Structures in Arrays
^^^^^^^^^^^^^^^^^^^^^^^^^^^

The generic package ``SPARK.Higher_Order.Reachability`` in file
``spark-higher_order-reachability.ads`` provides functions for reasoning about
acyclic linked structures stored in an array. They work on arrays that store
one or several linked structures using a ``Next`` function: for each cell in
the array, the index of the next cell is returned by ``Next``. The end of a
structure is marked by a special value ``No_Index``, which should not be a
valid index in the array. As an example, consider lists of integers stored in
an array, where the value 0 is used for ``No_Index``:

.. literalinclude:: /examples/ug__higher_order_reachability/memory_lists.ads
   :language: ada
   :lines: 7-15

In addition to the types of the indexes, of the cells, and of the array, the
package takes as parameters instances of functional sets and sequences of
indexes, which are used to describe the structures:

.. literalinclude:: /examples/ug__higher_order_reachability/memory_lists.ads
   :language: ada
   :lines: 17-21

The ``Reachability`` package can then be instantiated for our lists:

.. literalinclude:: /examples/ug__higher_order_reachability/memory_lists.ads
   :language: ada
   :lines: 23-30

The ``Reachability`` package defines three functions over these structures,
along with some lemmas that can be used to reason over them. Here are their
declarations, without their postconditions:

.. code-block:: ada

   function Is_Acyclic (X : Extended_Index; M : Memory_Type) return Boolean
   with
     Pre => X in M'Range | No_Index and then Valid_Memory (M);

   function Reachable_Set
     (X : Extended_Index; M : Memory_Type) return Memory_Index_Set
   with
     Pre => X in M'Range | No_Index and then Valid_Memory (M);

   function Model (X : Extended_Index; M : Memory_Type) return Sequence
   with
     Pre =>
       X in M'Range | No_Index
       and then Valid_Memory (M)
       and then Is_Acyclic (X, M);

They all take as parameters an index ``X``, which may be ``No_Index``, and an
array ``M``, which should be well formed, as expressed by the function
``Valid_Memory``: ``M`` should start at ``Index_Type'First`` and the ``Next``
value of each of its cells should be either a valid index in ``M`` or
``No_Index``. The function ``Is_Acyclic`` returns True if the linked
structure starting at ``X`` in ``M`` does not contain cycles. The function
``Reachable_Set`` returns the functional set of all the indices in the array
that can be reached from ``X`` by calling ``Next`` repeatedly. Finally, the
function ``Model`` computes a functional sequence that stores the indices
reachable from ``X`` in the reverse of the order in which they occur: the first
element of the sequence is the last index of the structure, the one whose
``Next`` is ``No_Index``, and the last element is ``X`` itself.

The recursive definitions of these functions are given by lemmas which are
instantiated automatically by default, as in the instance ``Lists`` above. As
this might lead to instantiation loops, causing the context to grow too much for
complex proofs, it can be disabled by setting the generic parameter
``Automatically_Instantiate_Definitions`` to ``False``. The definitions can
then be made available for the verification of a subprogram by calling the
``Disclose_*`` procedures of the package inside it.

The other lemmas of the package fall into two categories:

* Lemmas stating general properties of reachability, for example that it is
  transitive (``Lemma_Reachable_Transitive``) or that the model of a
  reachable cell is a prefix of the model of the head of the structure
  (``Lemma_Model_Is_Prefix``).

* Lemmas computing the new values of ``Is_Acyclic``, ``Reachable_Set``, and
  ``Model`` after a modification of the array. Lemmas with the ``_Preserved``
  suffix handle the case where a whole structure is left unchanged, lemmas
  with the ``_Preserved_Until`` suffix the case where a segment of a structure
  is left unchanged, and lemmas with the ``_After_Set`` suffix the case where
  the ``Next`` value of a single cell is updated.

As an example, the function ``Contains_Value`` below searches for a value in the
list starting at index ``X`` in our array of cells. Its postcondition is
expressed using ``Reachable_Set``:

.. literalinclude:: /examples/ug__higher_order_reachability/linked_lists.ads
   :language: ada
   :linenos:

Thanks to the automatic instantiation of the recursive definition of
``Reachable_Set``, the loop invariants and the loop variant are verified
without calling any lemma. When the loop exits, ``C`` is ``No_Index``, so its
reachable set is empty. The assertion after the loop states this fact, from
which the postcondition follows using the loop invariant:

.. literalinclude:: /examples/ug__higher_order_reachability/linked_lists.adb
   :language: ada
   :linenos:

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

In the examples above, procedures ``Foo`` and ``Bar`` have the same
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

All functions and procedures are annotated with Global, and Pre, Post if
necessary. The Global contracts are most of the time ``In_Out`` for
``File_System``, even in ``Put`` or ``Get`` procedures that update the
current column and/or line. Functions have an ``Input`` global
contract. The only functions with ``Global => null`` are the functions
``Get`` and ``Put`` in the generic packages that have a similar
behavior as sprintf and sscanf.

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
   aspect, it is not possible to model its action on the files
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

-  ``Name_Error`` would require checking availability on disk beforehand.

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
``Page_Length`` has been specified, e.g., if the lines are unbounded,
it is possible to have a ``Col`` greater than ``Count'Last`` and
therefore have a ``Layout_Error`` raised when calling ``Col``.

Not only the handling is partial, but it is also impossible to prove
preconditions when working with two files or more. Since
``Line_Length`` etc. attributes are stored in the ``File_System``, it
is not possible to prove that the ``Line_Length`` of ``File_2`` has not
been modified when running any procedure that does input-output on ``File_1``.

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

The Ada Standard Library
^^^^^^^^^^^^^^^^^^^^^^^^

``Interfaces.C.Strings`` is a library that provides an Ada interface to
allocate, reference, update and free C strings.

The provided preconditions protect users from getting
``Dereference_Error`` and ``Update_Error``. However, those
preconditions do not protect against ``Storage_Error`` and in general against
leaking memory allocated by ``New_String`` and ``New_Char_Array``.

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
aspect. Indeed, calling those functions twice in a row with the
same parameters would return different objects.

Precise C Strings Interface
^^^^^^^^^^^^^^^^^^^^^^^^^^^

The annotations on ``Interfaces.C.Strings`` do not allow for a precise handling
of the content of strings as it cannot reason about potential aliases between
strings. As an alternative, when precision is required, two wrappers over
``Interfaces.C.Strings`` are provided in the |SPARK| library (see
:ref:`SPARK Library`).

In the package ``SPARK.C.Strings``, C strings are handled as |SPARK| pointers.
Absence of aliasing and memory safety is ensured through ownership (see
:ref:`Memory Ownership Policy`). This handling allows for safe allocation and
reclamation of memory as well as precise contracts on the content of strings.
However, like for regular pointers, ``Storage_Error`` might occur due to
memory shortage.

Like for ``Interfaces.C.Strings``, the ``To_Chars_Ptr`` function is disallowed
but ``Free`` is retained. It is left as an assumption for the user to make sure
that it is only called on a pointer allocated through ``New_String`` or
``New_Char_Array`` and not on a value created in C code. Two additional
conversion functions are provided to convert to and from C strings coming from
``Interfaces.C.Strings`` but they cannot be used safely in |SPARK| and are
annotated with ``SPARK_Mode => Off``.

As opposed to ``Interfaces.C.Strings``, the content of each string is modeled
separately instead of collapsed together in a single abstract state and all
subprograms are annotated with postconditions modeling the content of
the string. This allows for a precise handling of C strings in |SPARK|.

The package ``SPARK.C.Constant_Strings`` offers an alternative to
``SPARK.C.Strings`` which does not enforce ownership at the cost of
immutability. Aliasing between C strings is allowed but the designated values
cannot be modified. The ``New_String`` and ``New_Char_Array`` are annotated with
``SPARK_Mode => Off`` as they can cause memory leaks. Instead, a version of
``To_Chars_Ptr`` taking as input an access to a constant ``char_array`` is
provided. The ``Update`` procedures are removed. It is left as an assumption
for the user to make sure that values of this type are never mutated by the
C code.

Here again, the content of each string is modeled separately and all
functions are annotated with postconditions modeling the content of
the string to allow for a precise handling of C strings in |SPARK|.

.. index:: address-to-access-conversion

Addresses to Access Conversions
-------------------------------

The run-time library ``System.Address_To_Access_Conversions`` enables
the user to convert ``System.Address`` values to general access-to-object
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

This allows introducing intermediate assertions to help the proof of some
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

* As an operand of an AND, OR, AND THEN, or OR ELSE operation which itself occurs
  in a supported context;

* As the THEN or ELSE branch of an IF expression which itself occurs in a
  supported context;

* As an alternative of a CASE expression which itself occurs in a supported
  context;

* As the condition of a quantified expression which itself occurs in a supported
  context;

* As a parameter to a call to either ``By`` or ``So`` which itself occurs in a
  supported context;

* As the body expression of a DECLARE expression which itself occurs in a
  supported context.
