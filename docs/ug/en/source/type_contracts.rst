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
  to express a property verified by objects of the (sub)type.
* A *type invariant* introduced by aspect ``Type_Invariant`` or ``Invariant``
  may be specified on the completion of a private type to express a property
  that is only guaranteed outside of the type scope.
* A *default initial condition* introduced by aspect
  ``Default_Initial_Condition`` on a private type specifies the initialization
  status and possibly properties of the default initialization for a type.

Note that |SPARK| does not yet support aspect ``Type_Invariant`` from Ada.

.. index:: range

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

.. index:: discriminant

Record Discriminants
---------------------

[Ada 83]

Record types can use discriminants to:

* define multiple variants and associate each component with a specific variant
* bound the size of array components

For example, the log introduced in :ref:`State Abstraction` could be
implemented as a discriminated record with a discriminant ``Kind`` selecting
between two variants of the record for logging either only the minimum and
maximum entries or the last entries, and a discriminant ``Capacity`` specifying
the maximum number of entries logged:

.. literalinclude:: /examples/tests/logging_discr/logging_discr.ads
   :language: ada
   :linenos:

Subtypes of ``Log_Type`` can specify fixed values for ``Kind`` and
``Capacity``, like in ``Min_Max_Log`` and ``Ten_Values_Log``. The discriminants
``Kind`` and ``Capacity`` are accessed like regular components, for example:

.. literalinclude:: /examples/tests/logging_discr/logging_discr.adb
   :language: ada
   :linenos:

Any attempt to access a component not present in a variable (because it is of a
different variant), or to access an array component outside its bounds, results
in raising an exception at run time. During analysis, |GNATprove| checks that
components accessed are present, and that array components are accessed within
bounds:

.. literalinclude:: /examples/tests/logging_discr/test.out
   :language: none

.. index:: predicate, Static_Predicate, Dynamic_Predicate

.. _Predicates:

Predicates
----------

[Ada 2012]

Predicates can be used on any subtype to express a property verified by objects of
the subtype at all times. Aspects ``Static_Predicate`` and ``Dynamic_Predicate``
are defined in Ada to associate a predicate with a subtype. Aspect
``Dynamic_Predicate`` allows to express more general predicates than aspect
``Static_Predicate``, at the cost of restricting the use of variables of the
subtype. The following table summarizes the main similarities and differences
between both aspects:

.. csv-table::
   :header: "Feature", "``Static_Predicate``", "``Dynamic_Predicate``"
   :widths: 3, 1, 1

   "Applicable to scalar subtype", "Yes", "Yes"
   "Applicable to array/record subtype", "No", "Yes"
   "Allows simple comparisons with static values", "Yes", "Yes"
   "Allows conjunctions/disjunctions", "Yes", "Yes"
   "Allows function calls", "No", "Yes"
   "Allows general Boolean properties", "No", "Yes"
   "Can be used in membership test", "Yes", "Yes"
   "Can be used as range in for-loop", "Yes", "No"
   "Can be used as choice in case-statement", "Yes", "No"
   "Can be used as prefix with attributes First, Last or Range", "No", "No"
   "Can be used as index subtype in array", "No", "No"

Aspect ``Predicate`` is specific to |GNAT Pro| and can be used instead of
``Static_Predicate`` or ``Dynamic_Predicate``. |GNAT Pro| treats it as a
``Static_Predicate`` whenever possible and as a ``Dynamic_Predicate`` in the
remaining cases, thus not restricting uses of variables of the subtype more than
necessary.

Predicates are inherited by subtypes and derived types. If a subtype or a
derived type inherits a predicate and defines its own predicate, both
predicates are checked on values of the new (sub)type. Predicates are restricted in
|SPARK| so that they cannot depend on variable input. In particular, a
predicate cannot mention a global variable in |SPARK|, although it can mention
a global constant.

|GNATprove| checks that all values assigned to a subtype with a predicate are
allowed by its predicate (for all three forms of predicate: ``Predicate``,
``Static_Predicate`` and ``Dynamic_Predicate``). |GNATprove| generates a
predicate check even in cases where there is no corresponding run-time check,
for example when assigning to a component of a record with a
predicate. |GNATprove| also uses the predicate information for proving
properties about the program.

..  examples in this section are expanded in the example code predicates.ads
    and should be kept in synch with this code.

Static Predicates
^^^^^^^^^^^^^^^^^

A static predicate allows specifying which values are allowed or forbidden in a
scalar subtype, when this specification cannot be expressed with :ref:`Scalar
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
of this subtype. Scalar ranges and static predicates can also be combined, and
static predicates can be specified on subtypes, derived types and new signed
integer types. For example, we may define ``Count`` as follows:

.. code-block:: ada

   type Count is new Natural with
     Static_Predicate => Count /= 10 and Count /= 100;

Any attempt to assign a forbidden value to variable ``Total`` results in
raising an exception at run time. During analysis, |GNATprove| checks that all
values assigned to ``Total`` are allowed.

Similarly, we can express that values of subtype ``Normal_Float`` are the *normal*
32-bits floating-point values (thus excluding *subnormal* values), assuming
here that ``Float`` is the 32-bits floating-point type on the target:

.. code-block:: ada

   subtype Normal_Float is Float with
     Static_Predicate => Normal_Float <= -2.0**(-126) or Normal_Float = 0.0 or Normal_Float >= 2.0**(-126);

Any attempt to assign a subnormal value to a variable of subtype ``Normal_Float``
results in raising an exception at run time. During analysis, |GNATprove|
checks that only normal values are assigned to such variables.

Dynamic Predicates
^^^^^^^^^^^^^^^^^^

A dynamic predicate allows specifying properties of scalar subtypes that cannot be
expressed as static predicates. For example, we can express that values of subtype
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

* when converting a value to the subtype with the predicate
* when returning from a call, for each in-out and out parameter passed by reference
* when declaring an object, except when there is no initialization expression
  and no subcomponent has a default expression

Thus, not all violations of the dynamic predicate are caught at run time. On
the contrary, during analysis, |GNATprove| checks that initialized variables
whose subtype has a predicate always contain a value allowed by the predicate.

.. index:: Invariant, Type_Invariant

.. _Type Invariants:

Type Invariants
---------------

[Ada 2012]

In |SPARK|, type invariants can only be specified on completions of private
types (and not directly on private type declarations). They express a property
that is only guaranteed outside of the immediate scope of the type bearing the
invariant. Aspect ``Type_Invariant`` is defined in Ada to associate an
invariant with a type. Aspect ``Invariant`` is specific to |GNAT Pro| and can be
used instead of ``Type_Invariant``.

|GNATprove| checks that, outside of the immediate scope of a type with an
invariant, all values of this type are allowed by its invariant.
In order to provide such a strong guarantee, |GNATprove| generates an invariant
check even in cases where there is no corresponding run-time check, for example
on global variables that are modified by a subprogram. |GNATprove| also uses
the invariant information for proving properties about the program.

..  examples in this section are expanded in the example code invariants.ads/b
    and should be kept in synch with this code.

As an example, let us consider a stack, which can be queried for the maximum of
the elements stored in it:

.. code-block:: ada

   package P is

      type Stack is private;

      function Max (S : Stack) return Element;

   private


In the implementation, an additional component is allocated for the maximum,
which is kept up to date by the implementation of the stack. This information is
a type invariant, which can be specified using a ``Type_Invariant`` aspect:

.. code-block:: ada

   private

      type Stack is record
         Content : Element_Array := (others => 0);
         Size    : My_Length := 0;
         Max     : Element := 0;
      end record with
        Type_Invariant => Is_Valid (Stack);

      function Is_Valid (S : Stack) return Boolean is
        ((for all I in 1 .. S.Size => S.Content (I) <= S.Max)
         and (if S.Max > 0 then
                  (for some I in 1 .. S.Size => S.Content (I) = S.Max)));

      function Max (S : Stack) return Element is (S.Max);

   end P;

Like for subtype predicates, the name of the type can be used inside the invariant
expression to refer to the current instance of the type. Here the subtype predicate
of ``Stack`` expresses that the ``Max`` field of a valid stack is the maximum of
the elements stored in the stack.

.. index:: Default_Initial_Condition; with value False

To make sure that the invariant holds for every value of type ``Stack`` outside
of the package ``P``, |GNATprove| introduces invariant checks in several
places. First, at the type declaration, it will make sure that the invariant
holds every time an object of type ``Stack`` is default initialized. Here, as
the stack is empty by default and the default value of ``Max`` is 0, the check
will succeed. It is also possible to forbid default initialization of objects of
type ``Stack`` altogether by using a :ref:`Default Initial Condition` of
``False``:

.. code-block:: ada

   type Stack is private with Default_Initial_Condition => False;

   type Stack is record
      Content : Element_Array;
      Size    : My_Length;
      Max     : Element;
   end record with Type_Invariant => Is_Valid (Stack);

A check is also introduced to make sure the invariant holds for every global
object declared in the scope of ``Stack`` after it has been initialized:

.. code-block:: ada

   package body P is
      The_Stack : Stack := (Content => (others => 1),
                            Size    => 5,
                            Max     => 0);
   begin
      The_Stack.Max := 1;
   end P;

Here the global variable ``The_Stack`` is allowed to break its invariant during
the elaboration of ``P``. The invariant check will only be done at the end of
the elaboration of ``P``, and will succeed.

In the same way, variables and parameters of a subprogram are allowed to break
their invariants in the subprogram body. Verification
conditions are generated to ensure that no invariant breaking value can leak
outside of ``P``. More precisely, invariant checks on subprogram parameters are
performed:

* when calling a subprogram visible outside of ``P`` from inside of ``P``. Such
  a subprogram can be either declared in the visible part of ``P`` or in another
  unit,
* when returning from a subprogram declared in the visible part of ``P``.

For example, let us consider the implementation of a procedure ``Push`` that
pushes an element of top of a stack. It is declared in the visible part of the
specification of ``P``:

.. code-block:: ada

   function Size (S : Stack) return My_Length;

   procedure Push (S : in out Stack; E : Element) with
     Pre => Size (S) < My_Length'Last;

   procedure Push_Zero (S : in out Stack) with
     Pre => Size (S) < My_Length'Last;

It is then implemented using an internal procedure ``Push_Internal`` declared
in the body of ``P``:

.. code-block:: ada

   procedure Push_Internal (S : in out Stack; E : Element) with
     Pre  => S.Size < My_Length'Last,
     Post => S.Size = S.Size'Old + 1 and S.Content (S.Size) = E
     and S.Content (1 .. S.Size)'Old = S.Content (1 .. S.Size - 1)
     and S.Max = S.Max'Old
   is
   begin
      S.Size := S.Size + 1;
      S.Content (S.Size) := E;
   end Push_Internal;

   procedure Push (S : in out Stack; E : Element) is
   begin
      Push_Internal (S, E);
      if S.Max < E then
         S.Max := E;
      end if;
   end Push;

   procedure Push_Zero (S : in out Stack) is
   begin
      Push (S, 0);
   end Push_Zero;

On exit of ``Push_Internal``, the invariant of ``Stack`` is broken. It is OK
since ``Push_Internal`` is not visible from outside of ``P``. Invariant checks
are performed when exiting ``Push`` and when calling it from inside
``Push_Zero``. They both succeed.
Note that, because of invariant checks on parameters, it is not allowed in
|SPARK| to call a function that is visible from outside ``P`` in the invariant
of ``Stack`` otherwise this would lead to a recursive proof. In particular, it
is not allowed to make ``Is_Valid`` visible in
the public declarations of ``P``. In the same way, the function ``Size`` cannot
be used in the invariant of ``Stack``. We also avoid using ``Size`` in the
contract of ``Push_Internal`` as it would have enforced additional invariant
checks on its parameter.

Checks are also performed for global variables accessed by subprograms inside
``P``. Even if it is allowed to break the invariant of a global variable when
inside the body of a subprogram declared in ``P``, invariant checks are
performed when calling and returning from every subprogram inside ``P``. For
example, if ``Push`` and ``Push_Internal`` are accessing directly the global
stack ``The_Stack`` instead of taking it as a parameter, there will be a failed
invariant check on exit of ``Push_Internal``:

.. code-block:: ada

   procedure Push_Internal (E : Element) with
     Pre  => The_Stack.Size < My_Length'Last
   is
   begin
      The_Stack.Size := The_Stack.Size + 1;
      The_Stack.Content (The_Stack.Size) := E;
   end Push_Internal;

   procedure Push (E : Element) is
   begin
      Push_Internal (E);
      if The_Stack.Max < E then
         The_Stack.Max := E;
      end if;
   end Push;

In this way, users will never have to use contracts to ensure that the invariant
holds on global variable ``The_Stack`` through local subprogram calls.

.. index:: Default_Initial_Condition

.. _Default Initial Condition:

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

.. literalinclude:: /examples/tests/logging_priv/logging_priv.ads
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

.. literalinclude:: /examples/tests/logging_priv/test.out
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

In general, GNATprove generates checks for the default value of a type when a
variable of this type is default initialized. This is not the case for private
types, as the default value of a private type declared in a library unit is
really the responsibility of the implementer of the library, not the user.
If the private type has a known discriminant
part, then default checks are done for any values of the discriminants.

If a private type has a ``Default_Initial_Condition``, then this
condition can act either as a precondition or as a postcondition of the default
value computation. If the ``Default_Initial_Condition`` does not refer to the
current type instance, or if it only refers to its discriminants, then it is
considered to be a precondition: it is the user of the private type who is
responsible for ensuring its validity. As such, the condition is assumed when
checking the default value of the private type, and it is checked each time a
variable of the type is default initialized. For example, in the following
example, we must have ``First < Last`` to be allowed to safely default
initialize our stack type:

.. code-block:: ada

   type Stack (First, Last : Positive) is private with
     Default_Initial_Condition => First < Last;

|GNATprove| will take advantage of this information when checking the default
value of ``Stack`` for run-time exceptions. For example, it will be able to
ensure that the predicate will hold if ``Stack`` is defined as follows:

.. code-block:: ada

      type Stack (First, Last : Positive) is record
         Content : Nat_Arr (First .. Last) := 0;
         Top     : Positive := First;
      end record with
        Predicate => Top in Content'Range;

Otherwise, the ``Default_Initial_Condition`` is handled as a postcondition of
the default value computation. It is checked once and for all when the
definition of the type is analyzed.
