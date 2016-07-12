.. _Type Contracts:

Type Contracts
==============

|SPARK| contains various features to constrain the values of a given type:

* A *scalar range* may be specified on a scalar type or subtype to bound its
  values.
* A *record discriminant* may be specified on a record type to distinguish
  between variants of the same record.
* A *predicate* introduced by aspect ``Static_Predicate``,
  ``Dynamic_Predicate`` or ``Predicate`` may be specified on a type or subtype
  to express a property verified by objects of the type.
* A *default initial condition* introduced by aspect
  ``Default_Initial_Condition`` on a private type specifies the initialization
  status and possibly properties of the default initialization for a type.

Note that |SPARK| does not yet support aspect ``Type_Invariant`` from Ada 2012.

.. _Scalar Ranges:

Scalar Ranges
-------------

[Ada 83]

Scalar types (signed integer types, modulo types, fixed-point types,
floating-point types) can be given a low bound and a high bound to specify that
values of the type must remain within these bounds. For example, the global
counter ``Total`` can never be negative, which can be expressed in its type:

.. code-block:: ada

   Total : Integer range 0 .. Integer'Last;

Any attempt to assign a negative value to variable ``Total`` results in raising
an exception at run time. During analysis, |GNATprove| checks that all values
assigned to ``Total`` are positive or null. The anonymous subtype above can
also be given an explicit name:

.. code-block:: ada

   subtype Nat is Integer range 0 .. Integer'Last;
   Total : Nat;

or we can use the equivalent standard subtype ``Natural``:

.. code-block:: ada

   Total : Natural;

or ``Nat`` can be defined as a derived type instead of a subtype:

.. code-block:: ada

   type Nat is new Integer range 0 .. Integer'Last;
   Total : Nat;

or as a new signed integer type:

.. code-block:: ada

   type Nat is range 0 .. Integer'Last;
   Total : Nat;

All the variants above result in the same range checks both at run-time and in
|GNATprove|. |GNATprove| also uses the range information for proving properties
about the program (for example, the absence of overflows in computations).

Record Discriminants
---------------------

[Ada 83]

Record types can use discriminants to:

* define multiple variants and associate each component to a specific variant
* bound the size of array components

For example, the log introduced in :ref:`State Abstraction` could be
implemented as a discriminated record with a discriminant ``Kind`` selecting
between two variants of the record for logging either only the minimum and
maximum entries or the last entries, and a discriminant ``Capacity`` specifying
the maximum number of entries logged:

.. literalinclude:: ../gnatprove_by_example/examples/logging_discr.ads
   :language: ada
   :linenos:

Subtypes of ``Log_Type`` can specify fixed values for ``Kind`` and
``Capacity``, like in ``Min_Max_Log`` and ``Ten_Values_Log``. The discriminants
``Kind`` and ``Capacity`` are accessed like regular components, for example:

.. literalinclude:: ../gnatprove_by_example/examples/logging_discr.adb
   :language: ada
   :linenos:

Any attempt to access a component not present in a variable (because it is of a
different variant), or to access an array component outside its bounds, results
in raising an exception at run time. During analysis, |GNATprove| checks that
components accessed are present, and that array components are accessed within
bounds:

.. literalinclude:: ../gnatprove_by_example/results/logging_discr.prove
   :language: none

.. _Predicates:

Predicates
----------

[Ada 2012]

Predicates can be used on any type to express a property verified by objects of
the type at all times. Aspects ``Static_Predicate`` and ``Dynamic_Predicate``
are defined in Ada 2012 to associate a predicate to a type. Aspect
``Dynamic_Predicate`` allows to express more general predicates than aspect
``Static_Predicate``, at the cost of restricting the use of variables of the
type. The following table summarizes the main similarities and differences
between both aspects:

.. csv-table::
   :header: "Feature", "``Static_Predicate``", "``Dynamic_Predicate``"
   :widths: 3, 1, 1

   "Applicable to scalar type", "Yes", "Yes"
   "Applicable to array/record type", "No", "Yes"
   "Allows simple comparisons with static values", "Yes", "Yes"
   "Allows conjunctions/disjunctions", "Yes", "Yes"
   "Allows function calls", "No", "Yes"
   "Allows general Boolean properties", "No", "Yes"
   "Can be used in membership test", "Yes", "Yes"
   "Can be used as range in for-loop", "Yes", "No"
   "Can be used as choice in case-statement", "Yes", "No"
   "Can be used as prefix with attributes First, Last or Range", "No", "No"
   "Can be used as index type in array", "No", "No"

Aspect ``Predicate`` is specific to |GNAT Pro| and can be used instead of
``Static_Predicate`` or ``Dynamic_Predicate``. |GNAT Pro| treats it as a
``Static_Predicate`` whenever possible and as a ``Dynamic_Predicate`` in the
remaining cases, thus not restricting uses of variables of the type more than
necessary.

Predicates are inherited by subtypes and derived types. If a subtype or a
derived type inherits a predicate and defines its own predicate, both
predicates are checked on values of the new type. Predicates are restricted in
|SPARK| so that they cannot depend on variable input. In particular, a
predicate cannot mention a global variable in |SPARK|, although it can mention
a global constant.

|GNATprove| checks that all values assigned to a type with a predicate are
allowed by its predicate. |GNATprove| generates a predicate check even in cases
where there is no corresponding run-time check, for example when assigning to a
component of a record with a predicate. |GNATprove| also uses the predicate
information for proving properties about the program.

..  examples in this section are expanded in the example code predicates.ads
    under gnatprove_by_example, and should be kept in synch with this code.

Static Predicates
^^^^^^^^^^^^^^^^^

A static predicate allows specifying which values are allowed or forbidden in a
scalar type, when this specification cannot be expressed with :ref:`Scalar
Ranges` (because it has *holes*). For example, we can express that the global
counter ``Total`` cannot be equal to ``10`` or ``100`` with the following
static predicate:

.. code-block:: ada

   subtype Count is Integer with
     Static_Predicate => Count /= 10 and Count /= 100;
   Total : Count;

or equivalently:

.. code-block:: ada

   subtype Count is Integer with
     Static_Predicate => Count in Integer'First .. 9 | 11 .. 99 | 101 .. Integer'Last;
   Total : Count;

Uses of the name of the subtype ``Count`` in the predicate refer to variables
of this type. Scalar ranges and static predicates can also be combined, and
static predicates can be specified on subtypes, derived types and new signed
integer types. For example, we may define ``Count`` as follows:

.. code-block:: ada

   type Count is new Natural with
     Static_Predicate => Count /= 10 and Count /= 100;

Any attempt to assign a forbidden value to variable ``Total`` results in
raising an exception at run time. During analysis, |GNATprove| checks that all
values assigned to ``Total`` are allowed.

Similarly, we can express that values of type ``Normal_Float`` are the *normal*
32-bits floating-point values (thus excluding *subnormal* values), assuming
here that ``Float`` is the 32-bits floating-point type on the target:

.. code-block:: ada

   subtype Normal_Float is Float with
     Static_Predicate => Normal_Float <= -2.0**(-126) or Normal_Float = 0.0 or Normal_Float >= 2.0**(-126);

Any attempt to assign a subnormal value to a variable of type ``Normal_Value``
results in raising an exception at run time. During analysis, |GNATprove|
checks that only normal values are assigned to such variables.

Dynamic Predicates
^^^^^^^^^^^^^^^^^^

A dynamic predicate allows specifying properties of scalar types that cannot be
expressed as static predicates. For example, we can express that values of type
``Odd`` and ``Even`` are distributed according to their name as follows:

.. code-block:: ada

   subtype Odd is Natural with
     Dynamic_Predicate => Odd mod 2 = 1;

   subtype Even is Natural with
     Dynamic_Predicate => Even mod 2 = 0;

or that values of type ``Prime`` are prime numbers as follows:

.. code-block:: ada

   type Prime is new Positive with
     Dynamic_Predicate => (for all Divisor in 2 .. Prime / 2 => Prime mod Divisor /= 0);

A dynamic predicate also allows specifying relations between components of a
record. For example, we can express that the values paired together in a record
are always distinct as follows:

.. code-block:: ada

   type Distinct_Pair is record
     Val1, Val2 : Integer;
   end record
     with Dynamic_Predicate => Distinct_Pair.Val1 /= Distinct_Pair.Val2;

or that a record stores pairs of values with their greatest common divisor as
follows:

.. code-block:: ada

   type Bundle_Values is record
     X, Y : Integer;
     GCD  : Natural;
   end record
     with Dynamic_Predicate => Bundle_Values.GCD = Get_GCD (Bundle_Values.X, Bundle_Values.Y);

or that the number of elements ``Count`` in a resizable table is always less
than or equal to its maximal number of elements ``Max`` as follows:

.. code-block:: ada

   type Resizable_Table (Max : Natural) is record
      Count : Natural;
      Data  : Data_Array(1 .. Max);
   end record
     with Dynamic_Predicate => Resizable_Table.Count <= Resizable_Table.Max;

A dynamic predicate also allows specifying global properties over the content
of an array. For example, we can express that elements of an array are stored
in increasing order as follows:

.. code-block:: ada

   type Ordered_Array is array (Index) of Integer
     with Dynamic_Predicate =>
       (for all I in Index => (if I < Index'Last then Ordered_Array(I) < Ordered_Array(I+1)));

or that a special end marker is always present in the array as follows:

.. code-block:: ada

   type Ended_Array is array (Index) of Integer
     with Dynamic_Predicate =>
       (for some I in Index => Ended_Array(I) = End_Marker);

Dynamic predicates are checked only at specific places at run time, as mandated
by the Ada Reference Manual:

* when converting a value to the type with the predicate
* when returning from a call, for each in-out and out parameter passed by reference
* when declaring an object, except when there is no initialization expression
  and no subcomponent has a default expression

Thus, not all violations of the dynamic predicate are caught at run time. On
the contrary, during analysis, |GNATprove| checks that initialized variables
whose type has a predicate always contain a value allowed by the predicate.

Default Initial Condition
-------------------------

[|SPARK|]

Private types in a package define an encapsulation mechanism that prevents
client units from accessing the implementation of the type. That boundary may
also be used to specify properties that hold for default initialized values of
that type in client units. For example, the log introduced in :ref:`State
Abstraction` could be implemented as a private type with a default initial
condition specifying that the size of the log is initially zero, where uses of
the name of the private type ``Log_Type`` in the argument refer to variables of
this type:

.. literalinclude:: ../gnatprove_by_example/examples/logging_priv.ads
   :language: ada
   :linenos:

This may be useful to analyze with |GNATprove| client code that defines a
variable of type ``Log_Type`` with default initialization, and then proceeds to
append values to this log, as procedure ``Append_To_Log``'s precondition
requires that the log size is not maximal:

.. code-block:: ada

   The_Log : Log_Type;
   ...
   Append_To_Log (The_Log, X);

|GNATprove|'s flow analysis also uses the presence of a default initial
condition as an indication that default initialized variables of that type are
considered as fully initialized. So the code snippet above would pass flow
analysis without messages being issued on the read of ``The_Log``. If the full
definition of the private type is in |SPARK|, |GNATprove| also checks that the
type is indeed fully default initialized, and if not issues a message like
here:

.. literalinclude:: ../gnatprove_by_example/results/logging_priv.flow
   :language: none

If partial default initialization of the type is intended, in general for
efficiency like here, then the corresponding message can be justified with
pragma ``Annotate``, see section :ref:`Justifying Check Messages`.

Aspect ``Default_Initial_Condition`` can also be specified without argument to
only indicate that default initialized variables of that type are considered as
fully initialized. This is equivalent to ``Default_Initial_Condition => True``:

.. code-block:: ada

   type Log_Type is private with
     Default_Initial_Condition;

The argument can also be ``null`` to specify that default initialized variables
of that type are *not* considered as fully initialized:

.. code-block:: ada

   type Log_Type is private with
     Default_Initial_Condition => null;

This is different from an argument of ``False`` which can be used to indicate
that variables of that type should always be explicitly initialized (otherwise
|GNATprove| will not be able to prove the condition ``False`` on the default
initialization and will issue a message during proof).
