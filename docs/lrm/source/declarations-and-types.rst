Declarations and Types
======================

No extensions or restrictions.

.. _declarations:

Declarations
------------

The view of an entity is in |SPARK| if and only if the corresponding
declaration is in |SPARK|. When clear from the context, we say *entity* instead
of using the more formal term *view of an entity*. If the initial declaration
of an entity (e.g., a subprogram, a private type, or a deferred
constant) requires a completion, it is possible that the initial declaration
might be in |SPARK| (and therefore can be referenced in |SPARK| code)
even if the completion is not in |SPARK|. [This distinction between views
is much less important in "pure" |SPARK| than in the case where SPARK_Mode is
used (as described in the SPARK Toolset User's Guide) to allow mixing
of |SPARK| and non-|SPARK| code.]

A type is said to *define full default initialization* if it is

  * a scalar type with a specified Default_Value; or

  * an access type; or

  * an array-of-scalar type with a specified Default_Component_Value; or

  * an array type whose element type defines default initialization; or

  * a record type, type extension, or protected type each of whose
    ``component_declarations`` either includes a ``default_expression`` or
    has a type which defines full default initialization and, in the case of
    a type extension, is an extension of a type which defines full default
    initialization; or

  * a task type; or

  * a private type whose Default_Initial_Condition aspect is specified to be a
    *Boolean_*\ ``expression``.

[The discriminants of a discriminated type play no role in determining
whether the type defines full default initialization.]


Types and Subtypes
------------------

No extensions or restrictions.


Type Declarations
~~~~~~~~~~~~~~~~~

No extensions or restrictions.


.. _subtype_declarations:

Subtype Declarations
~~~~~~~~~~~~~~~~~~~~

A ``constraint`` in |SPARK| cannot be defined using variable
expressions except when it is the ``range`` of a
``loop_parameter_specification``. Dynamic subtypes are permitted but
they must be defined using constants whose values may be derived from
expressions containing variables. Note that a formal parameter of a
subprogram of mode **in** is a constant and may be used in defining a
constraint. This restriction gives an explicit constant which can be
referenced in analysis and proof.

An expression with a *variable input* reads a variable or calls a
function which (directly or indirectly) reads a variable.

.. centered:: **Legality Rules**

.. _tu-subtype_declarations-01:

1. [A ``constraint``, excluding the ``range`` of a
   ``loop_parameter_specification``, shall not be defined using an
   expression with a variable input;
   see :ref:`expressions` for the statement of this rule.]

.. _etu-subtype_declarations-lr:


Classification of Operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No restrictions or extensions.

.. _subtype_predicates:

Subtype Predicates
~~~~~~~~~~~~~~~~~~

Static predicates and dynamic predicates are both in
|SPARK|, but subject to some restrictions.

.. centered:: **Legality Rules**

.. _tu-sf-subtype_predicates-01:

1. [A Dynamic_Predicate expression shall not have a variable input;
   see :ref:`expressions` for the statement of this rule.]

.. _etu-subtype_predicates-01:

.. _tu-sf-subtype_predicates-02:

2. If a Dynamic_Predicate applies to the subtype of a composite object,
   then a verification condition is generated to ensure that the object
   satisfies its predicate immediately after any subcomponent or slice
   of the given object is either

  * the target of an assignment statement or;

  * an actual parameter of mode **out** or **in out** in a call.

  [These verification conditions do not correspond to any run-time
  check. Roughly speaking, if object X is of subtype S, then verification
  conditions are generated as if an implicitly generated

     pragma Assert (X in S);

  were present immediately after any assignment statement or call which
  updates a subcomponent (or slice) of X.]

  [No such proof obligations are generated for assignments
  to subcomponents of the result object of an aggregate,
  an extension aggregate, or an update expression (see section
  :ref:`update-expressions`).
  These are assignment operations but not assignment statements.]

.. _etu-subtype_predicates-02:

.. _tu-sf-subtype_predicates-03:

3. A Static_Predicate or Dynamic_Predicate shall not apply to an effectively
   volatile type.

.. _etu-subtype_predicates-03:

.. _tu-subtype_predicates-vr:

.. centered:: **Verification Rules**

.. _tu-sf-subtype_predicates-04:

4. A Dynamic_Predicate expression shall always terminate.

.. _etu-subtype_predicates-04:

Objects and Named Numbers
-------------------------

.. _object-declarations:

Object Declarations
~~~~~~~~~~~~~~~~~~~

The Boolean aspect Constant_After_Elaboration may be specified as part of
the declaration of a library-level variable.
If the aspect is directly specified, the aspect_definition, if any,
shall be a static [Boolean] expression. [As with most Boolean-valued
aspects,] the aspect defaults to False if unspecified and to True if
it is specified without an aspect_definition.

A variable whose Constant_After_Elaboration aspect is True, or any part
thereof, is said to be *constant after elaboration*.
[The Constant_After_Elaboration aspect indicates that the variable will not
be modified after execution of the main subprogram begins
(see section :ref:`tasks-and-synchronization`).]

A stand-alone constant is a *constant with variable inputs* if its
initialization expression depends on:

  * A variable or parameter; or

  * Another *constant with variable inputs*

Otherwise, a stand-alone constant is a *constant without variable inputs*.

.. centered:: **Legality Rules**

.. _tu-object_declarations-01:

1. [The borrowed name of the expression of an object declaration defining a
   borrowing operation shall not have a variable input, except for a single
   occurrence of the root object of the expression;
   see :ref:`expressions` for the statement of this rule.]

.. centered:: **Verification Rules**

.. _tu-object_declarations-02:

2. Constants without variable inputs shall not be denoted in Global,
   Depends, Initializes or Refined_State aspect specifications.
   [Two elaborations of such a constant declaration will always
   yield equal initialization expression values.]

.. _etu-object_declarations-vr:

.. centered:: **Examples**

.. code-block:: ada

   A : constant Integer := 12;
   --  No variable inputs

   B : constant Integer := F (12, A);
   --  No variable inputs if F is a function without global inputs (although
   --  it could have global proof inputs)

   C : constant Integer := Param + Var;
   --  Constant with variable inputs


Number Declarations
~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Derived Types and Classes
-------------------------

The following rules apply to derived types in |SPARK|.

.. centered:: **Legality Rules**

.. _tu-derived_types-01:

1. A private type that is not visibly tagged but whose full view is tagged
   cannot be derived.

[The rationale for this rule is that, otherwise, given that visible operations
on this type cannot have class-wide preconditions and postconditions, it is
impossible to check the verification rules associated to overridding operations
on the derived type.]

.. _etu-derived_types:

Scalar Types
------------

The Ada RM states that, in the case of a fixed point type declaration,
"The base range of the type does not necessarily include the specified
bounds themselves". A fixed point type for which this inclusion does
not hold is not in |SPARK|.

For example, given

.. code-block:: ada

   type T is delta 1.0 range -(2.0 ** 31) .. (2.0 ** 31);

it might be the case that (2.0 ** 31) is greater
than T'Base'Last. If this is the case, then the type T is not in |SPARK|.

[This rule applies even in the case where the bounds
specified in the ``real_range_specification`` of an
``ordinary_fixed_point_definition`` define a null range.]

Array Types
-----------

No extensions or restrictions.

.. _discriminants:

Discriminants
-------------

The following rules apply to discriminants in |SPARK|.

.. centered:: **Legality Rules**

.. _tu-discriminants-01:

1. The type of a ``discriminant_specification`` shall be discrete.

.. _tu-discriminants-02:

2. A ``discriminant_specification`` shall not occur as part of a
   derived type declaration.

.. _tu-discriminants-03:

3. [The ``default_expression`` of a ``discriminant_specification``
   shall not have a variable input;
   see :ref:`expressions` for the statement of this rule.]

.. _etu-discriminants:

.. _record_types:

Record Types
------------

Default initialization expressions must not have variable inputs in |SPARK|.

.. centered:: **Legality Rules**

.. _tu-record_types-01:

1. [The ``default_expression`` of a ``component_declaration`` shall not
   have any variable inputs, nor shall it contain a name denoting
   the current instance of the enclosing type;
   see :ref:`expressions` for the statement of this rule.]

.. _etu-record_types:

[The rule in this section applies to any ``component_declaration``; this
includes the case of a ``component_declaration`` which is a
``protected_element_declaration``. In other words, this rule also applies to
components of a protected type.]

Tagged Types and Type Extensions
--------------------------------

.. centered:: **Legality Rules**

.. _tu-tagged_types-01:

1. No construct shall introduce a semantic dependence on the Ada language
   defined package Ada.Tags.  [See Ada RM 10.1.1 for the definition of semantic
   dependence.  This rule implies, among other things, that any use of the Tag
   attribute is not in |SPARK|.]

.. _tu-tagged_types-02:

2. The identifier External_Tag shall not be used as an
   ``attribute_designator``.

.. _etu-tagged_types:


Type Extensions
~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-type_extensions-01:

1. A type extension shall not be declared within a subprogram body, block
   statement, or generic body which does not also enclose the declaration of
   each of its ancestor types.

.. _etu-type_extensions:


Dispatching Operations of Tagged Types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Abstract Types and Subprograms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Interface Types
~~~~~~~~~~~~~~~

No extensions or restrictions.

.. _access-types:

Access Types
------------

In order to reduce the complexity associated with the specification
and verification of a program's behavior in the face of pointer-related
aliasing, |SPARK| supports only "owning" access-to-object types (described
below); other access types (including access-to-subprogram types and
access discriminants) are not in |SPARK|.

Restrictions are imposed on the use of "owning" access objects in order
to ensure, roughly speaking (and using terms that have not been defined yet),
that at any given point in a program's execution, there is a unique "owning"
reference to any given allocated object. The "owner" of that allocated
object is the object containing that "owning" reference. If an object's
owner is itself an allocated object then it too has an owner; this chain
of ownership will always eventually lead to a (single) nonallocated object.

Ownership of an allocated object may change over time (e.g., if an allocated
object is removed from one list and then appended onto another) but
at any given time the object has only one owner. Similarly, at any given time
there is only one access path (i.e., the name of a "declared" (as opposed
to allocated) object followed by a sequence of component selections,
array indexings, and access value dereferences) which yields a given
(non-null) access value. At least that's the general idea - this paragraph
oversimplifies some things (e.g., see "borrowing" and "observing"
below - these operations extend SPARK's existing "single writer,
multiple reader" treatment of concurrency and of aliasing to apply to
allocated objects), but hopefully it provides useful intuition.

This means that data structures which depend on having multiple
outstanding references to a given object cannot be expressed in the usual
way. For example, a doubly-linked list (unlike a singly-linked list)
typically requires being able to refer to a list element both from its
predecessor element and from its successor element; that would violate
the "single owner" rule. Such data structures can still be expressed in
|SPARK| (e.g., by storing access values in an array and then using array
indices instead of access values), but such data structures may be harder
to reason about.

The single-owner model statically prevents storage leaks because
a storage leak requires either an object with no outstanding pointers
to it or an "orphaned" cyclic data structure (i.e., a set of multiple
allocated objects each reachable from any other but with
no references to any of those objects from any object outside of the set).

For purposes of flow analysis (e.g., Global and Depends aspect
specifications), a read or write of some part of an allocated object is
treated like a read or write of the owner of that allocated object.
For example, an assignment to Some_Standalone_Variable.Some_Component.all is
treated like an assignment to Some_Standalone_Variable.Some_Component.
Similarly, there is no explicit mention of anything related to access types
in a Refined_State or Initializes aspect specification; allocated objects
are treated like components of their owners and, like components, they are
not mentioned in these contexts.
This approach has the benefit that the same |SPARK| language rules which
prevent unsafe concurrent access to non-allocated variables also
provide the same safeguards for allocated objects.

For purposes of determining global inputs and outputs, both memory allocation
and deallocation are considered to reference an external state abstraction
SPARK.Heap.Dynamic_Memory that has property Async_Writers. In particular, each
occurence of an allocator is considered to reference this state abstraction as
an input. [In other words, an allocator can be treated like a call to a
volatile function which takes the allocated object as an actual parameter and
references the mentioned state abstraction as an Input global.] Similarly,
instances of the predefined generic Ada.Unchecked_Deallocation procedure behave
as if the generic procedure would be annotated with the following contract:

.. code-block:: ada

   procedure Ada.Unchecked_Deallocation (X : in out Name) with
     Depends => (SPARK.Heap.Dynamic_Memory => SPARK.Heap.Dynamic_Memory,
                 X => null, null => X);

so each call to an instance of this procedure is also considered to reference
the mentioned state abstraction.

The rules which accomplish all of this are described below.

.. centered:: **Static Semantics**

Only the following (named or anonymous) access types are in |SPARK|:

- a (named) pool-specific access type,

- the anonymous type of a stand-alone object (including a generic formal **in**
  mode object) which is not Part_Of a protected object,

- the anonymous type of an object renaming declaration, or

- an anonymous type occurring as a parameter type, or as a function result type
  of a traversal function (defined below).

[Redundant: For example, named general access types, access discriminants,
and access-to-subprogram types are not in |SPARK|.]

Such a type is said to be an *owning* access type when it is an
access-to-variable type, and an *observing* access type when it is an
access-to-constant type.

User-defined storage pools are not in |SPARK|; more specifically, the package
System.Storage_Pools, Storage_Pool aspect specifications, and the Storage_Pool
attribute are not in |SPARK|.

A composite type is also said to be an *owning* type if it has an
access subcomponent [redundant: , regardless of whether the subcomponent's
type is access-to-constant or access-to-variable].

Privacy is ignored in determining whether a type is an owning or
observing type. A generic formal private type is not an owning type
[redundant: , although the corresponding actual parameter in an instance
of the generic might be an owning type].
A tagged type shall not be an owning type.
A composite type which is not a by-reference type shall not be an owning type.
[Redundant: The requirement than an owning type must be a by-reference
type is imposed in part in order to avoid problematic scenarios involving
a parameter of an owning type passed by value in the case where the
call propagates an exception instead of returning normally. SPARK programs
are not supposed to raise exceptions, but this rule still seems desirable.]

An object of an owning access type is said to be an *owning* object;
an object of an observing access type is said to be an *observing* object.
An object that is a part of an object of an owning or observing type, or that
is part of a dereference of an access value is said to be a *managed* object.

In the case of a constant object of an access-to-variable type where the
object is not a stand-alone object and not a formal parameter (e.g.,
if the object is a subcomponent of an enclosing object or is designated
by an access value), a dereference of the object provides a constant
view of the designated object [redundant: , despite the fact that the
object is of an access-to-variable type. This is
because a subcomponent of a constant is itself a constant and a dereference
of a subcomponent is treated, for purposes of analysis, like a
subcomponent].

A function is said to be a *traversal function* if the result type of the
function is an anonymous access-to-object type, the function has at least one
formal parameter, and the function's first parameter is of an access type
[redundant: , either named or anonymous]. The traversal function is said to be
an *observing traversal function* if the result type of the function is an
anonymous access-to-constant type, and a *borrowing traversal function* if the
result type of the function is an anonymous access-to-variable type. The first
parameter of the function is called the *traversed* parameter. [Redundant: We
will see later that if a traversal function yields a non-null result, then that
result is "reachable" from the traversed parameter in the sense that it could
be obtained from the traversed parameter by some sequence of component
selections, array indexing operations, and access value dereferences.]

The *root object* of a name that denotes an object is defined as follows:

- if the name is a component_selection, an indexed_component, a slice,
  or a dereference (implicit or explicit)
  then it is the root object of the prefix of the name;

- if the name denotes a call on a traversal function,
  then it is the root object of the name denoting the actual
  traversed parameter;

- if the name denotes an object renaming, the root object is the
  root object of the renamed name;

- if the name is a function_call, and the function called is not a traversal
  function, the root object is the result object of the call;

- if the name is a qualified_expression or a type conversion, the root
  object is the root object of the operand of the name;

- otherwise, the name statically denotes an object and the root
  object is the statically denoted object.

Two names are said to be *potential aliases* when:

- both names statically denote the same entity [redundant: , which
  might be an object renaming declaration]; or

- both names are selected components, they have the same selector, and
  their prefixes are potential aliases; or

- both names are indexed components, their prefixes are potential
  aliases, and if all indexing expressions are static then each
  pair of corresponding indexing expressions have the same value; or

- both names are slices, their prefixes are potential aliases, and
  if both discrete_ranges are static ranges then the two
  discrete_ranges overlap; or

- one name is a slice and the other is an indexed component, their
  prefixes are potential aliases, and if both the discrete_range and
  the indexing expression are static then the value of the indexing
  expression is within the range; or

- one name is a slice whose prefix is a potential alias of the other name
  and the other name is neither a slice nor an indexed component; or

- both names are dereferences and their prefixes are potential aliases; or

- at least one name denotes an object renaming declaration, and the other
  is a potential alias with the object_name denoting the renamed entity.

Two names N1 and N2 are said to *potentially overlap* if

- some prefix of N1 is a potential alias of N2 (or vice versa); or

- N1 is a call on a traversal function and the actual traversed
  parameter of the call potentially overlaps N2 (or vice versa).

[Note that for a given name N which denotes an object of an access
type, the names N and N.all potentially overlap. Access value dereferencing
is treated, for purposes of this definition, like record component selection
or array indexing.]

The prefix and the name that are potential aliases are called the
*potentially aliased parts* of the potentially overlapping names.

A name that denotes a managed object can be in one of the
following ownership states: Unrestricted, Observed, Borrowed, or Moved.

A given name may take on different states at different points in the
program. For example, within a block_statement which declares an observer
(observers have not been defined yet), a name might have a state of Observed
while having a state of Unrestricted immediately before and immediately
after the block_statement. [Redundant: This is a compile-time notion;
no object-to-state mapping of any sort is maintained at runtime.]

In the Unrestricted state, no additional restrictions are imposed on the
use of the name. In particular, if the name denotes a variable
of an access-to-variable type then a dereference of the name provides a
variable view.

In the Observed state, the name provides a constant view (even if the
named object is a variable). If it denotes an access object then
a dereference of the name provides a constant view [redundant: , even if
the object is of an access-to-variable type].

In the Moved state, the name is unusable for reading
(although the name itself can be assigned to).

In the Borrowed state, the name is unusable for writing, observing and
borrowing (see below).

A name that denotes a managed object has an initial ownership state
of Unrestricted unless otherwise specified.
Certain constructs (described below) are said to *observe*, *borrow*,
or *move* the value of a managed object; these may change the ownership
state (to Observed, Borrowed, or Moved respectively) of a name within a
certain portion of the program text (described below). In the first two
cases (i.e. observing and borrowing), the ownership state of a name
reverts to its previous value at the end of this region of text.

The following operations *observe* a name that denotes a managed object
and identify a corresponding *observer*:

- An assignment operation that is used to initialize an access object,
  where this target object (the observer) is a stand-alone variable of an
  anonymous access-to-constant type, or a constant (including a formal
  parameter of a procedure or generic formal object of mode **in**) of an
  anonymous access-to-constant type.

  The source expression of the assignment shall be either a name denoting a
  part of a stand-alone object or of a parameter, or a call on a traversal
  function whose result type is an (anonymous) access type.  If the source of
  the assignment is a call on a traversal function then the name being observed
  denotes the actual traversed parameter of the call. Otherwise the name being
  observed denotes the source of the assignment.

- Inside the body of a borrowing traversal function, an assignment operation
  that is used to initialize an access object, where this target object (the
  observer) is a stand-alone object of an anonymous access-to-variable type
  [redundant: which does not include a formal parameter of a procedure or
  generic formal object of mode **in**] and the source expression of the
  assignment is either directly or indirectly a name denoting a part of the
  traversed parameter for the traversal function. The indirect case occurs when
  the source expression denotes a part of a call to another traversal function
  whose argument for its own traversed parameter respects the same constraint
  [redundant: of being either directly or indirectly a name denoting a part of
  the traversed parameter for the traversal function]. The name being observed
  denotes the traversed parameter for the traversal function whose body is
  considered.

- An assignment operation that is used to initialize a constant object
  (including a generic formal object of mode **in**) of an owning composite
  type. The name being observed denotes the source of the assignment. The
  initialized object is the observer.

- A procedure call where an actual parameter is a name denoting a managed
  object, and the corresponding formal parameter is of mode **in** and composite
  or aliased. The name being observed denotes the actual parameter.  The formal
  parameter is the observer.

Such an operation is called an *observing operation*.

In the region of program text beween the point where a name denoting a
managed object is observed and the end of the scope of the observer, the
ownership state of the name is Observed. While a name that denotes a managed
object is in the Observed state it provides a constant view
[redundant: , even if the name denotes a variable].

At the point where a name that denotes a managed object is observed,
every name of a reachable element of the object is observed.

The following operations *borrow* a name that denotes a managed object
and identify a corresponding *borrower*:

- An assignment operation that is used to initialize an access object, where
  this target object (the borrower) is a stand-alone variable of an anonymous
  access-to-variable type, or a constant (including a formal parameter of a
  procedure or generic formal object of mode **in**) of a (named or anonymous)
  access-to-variable type, unless this assignment is already an *observing
  operation* inside the body of a borrowing traversal function, per the rules
  defining *observe* above.

  The source expression of the assignment shall be either a name denoting a
  part of a stand-alone object or of a parameter, or a call on a traversal
  function whose result type is an (anonymous) access-to-variable type.  If the
  source of the assignment is a call on a traversal function then the name
  being borrowed denotes the actual traversed parameter of the call. Otherwise
  the name being borrowed denotes the source of the assignment.

- A call (or instantiation) where the (borrowed) name denotes an actual
  parameter that is a managed object other than an owning access object, and
  the formal parameter (the borrower) is of mode **out** or **in out** (or the
  generic formal object is of mode **in out**).

- An object renaming where the (borrowed) name is the object_name denoting the
  renamed object. In this case, the renamed object shall not be in the Observed
  or Borrowed state. The newly declared name is the borrower.

Such an operation is called a *borrowing operation*.

The *borrowed name* of the source of a borrow operation is the smallest
name that is borrowed in the borrow operation.

In the region of program text beween the point where a name denoting a
managed object is borrowed and the end of the scope of the borrower, the
ownership state of the name is Borrowed.

An indirect borrower of a name is defined to be a borrower either of
a borrower of the name or of an indirect borrower of the name.
A direct borrower of a name is just another term for a borrower of
the name, usually used together with the term "indirect borrower".
The terms "indirect observer" and "direct observer" are defined analogously.

While a name that denotes a managed object is in the Borrowed state it
provides a constant view [redundant: , even if the name denotes a variable].
Furthermore, the only permitted read of a managed object in the Borrowed
state is the introduction of a new observer of the object. Within the
scope of such a new observer any direct or indirect borrower
of the original name similarly enters the Observed state and provides
only a constant view.

At the point where a name that denotes a managed object is borrowed,
every name of a reachable element of the object is borrowed.

The following operations are said to be *move* operations:

- An assignment operation, where the target is a variable or return object (see
  Ada RM 6.5) of an owning type.

  [Redundant: In the case of a formal parameter of an access type of mode **in
  out** or **out**, this includes all assignments to or from such a formal
  parameter: copy-in before the call, copy-back after the call, and any
  assignments to or from the parameter during the call.]

- An assignment operation where the target is part of an aggregate of an owning
  type.

[Redundant: Passing a parameter by reference is not a move operation.]

A move operation results in a transfer of ownership. The state of
the source object of the assignment operation becomes Moved and
remains in this state until the object is assigned another value.

[Redundant: Roughly speaking, any access-valued parts of an object in the
Moved state can be thought of as being "poisoned"; such a poisoned object
is treated analogously to an uninitialized object in the sense that various
rules statically prevent the reading of such a value. Thus, an assignment
like::

   Pointer_1 : Some_Access_Type := new Designated_Type'(...);
   Pointer_2 : Some_Access_Type := Pointer_1;

does not violate the "single owner" rule because the move operation
poisons Pointer_1, leaving Pointer_2 as the unique owner of the
allocated object. Any attempt to read such a poisoned value is detected and
rejected.

Note that a name may be "poisoned" even if its value is "obviously" null.
For example, given::

   X : Linked_List_Node := (Data => 123, Link => null);
   Y : Linked_List_Node := X;

X.Link is poisoned by the assignment to Y.]

.. centered:: **Legality Rules**

[Redundant: For clarity of presentation, some legality rules are stated in the
preceding "Static Semantics" section (e.g., the rule that an owning type shall
not be a tagged type; stating that rule earlier eliminates the need to say
anything about the circumstances, if any, under which a class-wide type might
be an owning type).]

..  _tu-access_types-01:

1. At the point of a move operation the state of the source object (if any) and
   all of its reachable elements shall be Unrestricted. After a move operation,
   the state of any access parts of the source object (if there is one) becomes
   Moved.

.. _tu-access_types-02:

2. An owning object's state shall be Moved or Unrestricted at any point where

   - the object is the target of an assignment operation; or
   - the object is part of an actual parameter of mode **out** in a call.

   [Redundant: In the case of a call, the state of an actual parameter of mode
   **in** or **in out** remains unchanged (although one might choose to think
   of it as being borrowed at the point of the call and then "unborrowed" when
   the call returns - either model yields the same results); the state of an
   actual parameter of mode **out** becomes Unrestricted.]

.. _tu-access_types-03:

3. If the target of an assignment operation is an object of an anonymous
   access-to-object type (including copy-in for a parameter), then the source
   shall be a name denoting a part of a stand-alone object, a part of a
   parameter, or a part of a call to a traversal function.

   [Redundant: One consequence of this rule is that every allocator is of a
   named access type.]

.. _tu-access_types-04:

4. A declaration of a stand-alone object of an anonymous access type shall have
   an explicit initial value and shall occur immediately within a subprogram
   body, an entry body, or a block statement.

   [Redundant: Because such declarations cannot occur immediately within a
   package declaration or body, the associated borrowing/observing operation is
   limited by the scope of the subprogram, entry or block statement. Thus, it
   is not necessary to add rules restricting the visibility of such
   declarations.]

.. _tu-access_types-05:

5. A return statement that applies to a traversal function that has an
   anonymous access-to-constant (respectively, access-to-variable) result type,
   shall return either the literal null or an access object denoted by a direct
   or indirect observer (respectively, borrower) of the traversed parameter.
   [Redundant: Roughly speaking, a traversal function always yields either null
   or a result which is reachable from the traversed parameter.]

.. _tu-access_types-06:

6. If a prefix of a name is of an owning type, then the prefix shall denote
   neither a non-traversal function call, an aggregate, an allocator, nor any
   other expression whose associated object is (or, as in the case of a
   conditional expression, might be) the same as that of such a forbidden
   expression (e.g., a qualified expression or type conversion whose operand
   would be forbidden as a prefix by this rule).

.. _tu-access_types-07:

7. For an assignment statement where the target is a stand-alone object of an
   anonymous access-to-object type:

   - If the type of the target is an anonymous access-to-variable type (an
     owning access type), and the target was declared as a local variable in
     the body of a borrowing traversal function, whose initialization
     expression was either directly or indirectly a name denoting a part of the
     traversed parameter for the traversal function, then the source shall be
     an owning access object [redundant: denoted by a name that is not in the
     Moved state, and] whose root object is the target object itself;

   - If the type of the target is an anonymous access-to-variable type (an
     owning access type), and the previous case does not apply, the source
     shall be an owning access object denoted by a name that is in the
     Unrestricted state, and whose root object is the target object itself;

   - If the type of the target is an anonymous access-to-constant type (an
     observing access type), the source shall be an owning access object
     denoted by a name that is not in the Moved state, and whose root object is
     not in the Moved state and is not declared at a statically deeper
     accessibility level than that of the target object.

.. _tu-access_types-08:

8. At the point of a dereference of an object, the object shall not be in the
   Moved or Borrowed state.

.. _tu-access_types-09:

9. At the point of a read of an object, or of passing an object as an actual
   parameter of mode **in** or **in out**, or of a call where the object is a
   global input of the callee, neither the object nor any of its reachable
   elements shall be in the Moved or Borrowed state.

   At the point of a return statement, or at any other point where a call
   completes normally (e.g., the end of a procedure body), no inputs or outputs
   of the callee being returned from shall be in the Moved state.  In the case
   of an input of the callee which is not also an output, this rule may be
   enforced at the point of the move operation (because there is no way for the
   moved input to transition out of the Moved state), even in the case of a
   subprogram which never returns.

   Similarly, at the end of the elaboration of both the declaration and of the
   body of a package, no reachable element of an object denoted by the name of
   an initialization_item of the package's Initializes aspect or by an input
   occuring in the input_list of such an initialization_item shall be in the
   Moved state.

   The source of a move operation shall not be a part of a library-level
   constant without variable inputs.

.. _tu-access_types-10:

10. If the state of a name that denotes a managed object is Observed, the name
    shall not be moved, borrowed, or assigned.

.. _tu-access_types-11:

11. If the state of a name that denotes a managed object is Borrowed, the name
    shall not be moved, borrowed, observed, or assigned.

.. _tu-access_types-12:

12. At the point of a call, any name that denotes a managed object that is a
    global output of the callee (i.e., an output other than a parameter of the
    callee or a function result) shall not be in the Observed or Borrowed
    state.  Similarly, any name that denotes a managed object that is a global
    input of the callee shall not be in the Moved or Borrowed state.

.. _tu-access_types-13:

13. The prefix of an Old or Loop_Entry attribute reference shall not be of an
    owning or observing type unless the prefix is a function_call and the
    called function is not a traversal function.

.. centered:: **Verification Rules**

.. _tu-access_types-14:

14. When an owning access object other than a borrower, an observer,
    or an object in the Moved state is finalized, or when such an object
    is passed as a part of an actual parameter of mode **out**, its value
    shall be null.

    [Redundant: This rule disallows storage leaks. Without this rule,
    it would be possible to "lose" the last reference to an allocated
    object.]

    [Redundant: This rule applies to any finalization associated with a
    call to an instance of Ada.Unchecked_Deallocation. For details, see
    the Ada RM 13.11.2 rule "Free(X), ... first performs finalization of
    the object designated by X".]

.. _etu-access_types:

Declarative Parts
-----------------

No extensions or restrictions.
