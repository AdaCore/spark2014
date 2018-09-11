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

.. centered:: **Verification Rules**

.. _tu-object_declarations-01:

1. Constants without variable inputs shall not be denoted in Global,
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

1. If at least one nondiscriminant component (either explicitly
   declared or inherited) of a record type or type extension either is
   of a type which defines full default initialization or is declared
   by a ``component_declaration`` which includes a
   ``default_expression``, and if that component's type has at least
   one elementary nondiscriminant part, then the record type or type
   extension shall define full default initialization.

   [The enforcement of this rule may require looking at the
   ``full_type_declaration`` of a ``private_type`` declaration if the
   private type's Default_Initial_Condition aspect is not specified.]

   [In the unusual case of a nondiscriminant component which has no
   nondiscriminant scalar parts (e.g., an array of null records),
   the preceding "at least one elementary" wording means that the component
   is ignored for purposes of this rule.]

.. _tu-record_types-02:

2. [The ``default_expression`` of a ``component_declaration`` shall not
   have any variable inputs, nor shall it contain a name denoting
   the current instance of the enclosing type;
   see :ref:`expressions` for the statement of this rule.]

.. _etu-record_types:

[The rules in this section apply to any ``component_declaration``; this
includes the case of a ``component_declaration`` which is a
``protected_element_declaration``. In other words, these rules also apply to
components of a protected type.]

Tagged Types and Type Extensions
--------------------------------

.. centered:: **Legality Rules**

.. _tu-tagged_types-01:

1.  No construct shall introduce a semantic dependence on the Ada
    language defined package Ada.Tags.
    [See Ada RM 10.1.1 for the definition of semantic dependence.
    This rule implies, among other things, that any use of the Tag attribute
    is not in |SPARK|.]

.. _tu-tagged_types-02:

2.  The identifier External_Tag shall not be used as an
    ``attribute_designator``.

.. _etu-tagged_types:


Type Extensions
~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-type_extensions-01:

1.  A type extension shall not be declared within a
    subprogram body, block statement, or generic body which does not
    also enclose the declaration of each of its ancestor types.

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

Access Types
------------

In order to reduce the complexity associated with the specification
and verification of a program's behavior in the face of pointer-related
aliasing, |SPARK| supports only "owning" access-to-object types (described
below); other access types (including access-to-subprogram types and
access discriminants) are are not in |SPARK|.

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
allocated objects each reachable from the any other but with
no references to any of those objects from any object outside of the set).

For purposes of flow analysis (e.g., Global and Depends aspect
specifications), a read or write of some part of an allocated object is
treated like a read or write of the owner of that allocated object.
For example, an assignment to Some_Standalone_Variable.Some_Component.all is
treated like an assignment to Some_Standalone_Variable.Some_Component .
Similarly, there is no explicit mention of anything related to access types
in a Refined_State or Initializes aspect specification; allocated objects
are treated like components of their owners and, like components, they are
not mentioned in these contexts.
This approach has the benefit that the same |SPARK| language rules which
prevent unsafe concurrent access to non-allocated variables also
provide the same safeguards for allocated objects.

The rules which accomplish all of this are described below.

.. centered:: **Static Semantics**

The following aspect may be specified for a
pool-specific access-to-object type, a stand-alone object of an anonymous
access-to-object type (including a generic formal in-mode object),
a composite type (including a partial view of a type), or a function:
[TBD: generic formal non-scalar types]

Ownership

  The Ownership aspect is of type Boolean. If directly specified,
  the aspect_definition shall be a static expression. The Ownership
  aspect of a type (as opposed to of a function or of an object) is
  a type-related aspect.
  [TBD: saying that one aspect is type-related and nonoverridable in
  some contexts but not in others is something new. Is this ok?]
  If not otherwise specified (either explicitly or, in the case of an
  derived type, by inheritance) the value of the Ownership aspect of
  an entity is determined as follows:

     - For a pool-specific access type, the aspect value is False.

     - For a standalone object of an anonymous access-to-object type,
       the aspect value is that of the type of the initial value (or, in the
       case of a generic formal In-mode object, the type of the default value)
       if any such value is present; otherwise the aspect value is False.

  -  - For a composite type, the aspect value is the disjunction (i.e., "or")
       of the Ownership aspect values of the component types of the
       composite type, of any partial view of the type, and,
       in the case of a type extension, of the ancestor
       type and any progenitor types. If this disjunction is True, then
       any explicit Ownership aspect specification for any view of the type
       shall specify the value True.

     - For a function, the aspect value is True if the function is a
       dispatching operation and the aspect is True for the corresponding
       primitive subprogram of some ancestor; otherwise the aspect value
       is False. An explicit Ownership aspect specification for a function
       shall be confirming if the value False is specified.
       [TBD: somehow relax this if Extensions_Visible => False?]

  For an untagged type, the Ownership aspect is non-overridable.

  If a type has a partial view, the Ownership aspect may be specified
  explicitly only on the partial view and, if specified True, the full
  type shall not be an elementary type nor an untagged private or
  derived type with Ownership aspect False; furthermore, if the Ownership
  aspect for the full type would be True if not explicitly specified, the
  Ownership aspect of the partial view shall be True, either by inheritance
  from an ancestor type or by an explicit specification.
  [TBD: interactions with generic formal types].

An access-to-variable type with Ownership aspect True is said to be
an *owning* access type. Similarly, an object of an owning access type
is called an owning access object. An access-to-constant type with
Ownership aspect True is said to be an *observing* access type. Similarly,
an object of an observing access type is called an observing access object.
An object that is a part of an object of type with Ownership
aspect True, or a part of the dereference of an owning or observing
access object, is said to be a *managed* object.

Any composite type with Ownership aspect True is defined to be a
by-reference type (see 6.2).

A function with Ownership aspect True whose result type is an anonymous
access-to-object type is said to be a *traversal function* if it has
has exactly one parameter of an anonymous access-to-object type with
matching constant vs. variable access to the designated object; that
parameter is called the *traversed* parameter.
[TBD: use a new Traversal aspect instead of Ownership aspect here?]

The Ownership aspect is also defined (although not directly specifiable)
for anonymous access-to-object types as follows:

  - for the type of a standalone object, the aspect value is that of
    the object;

  - for the result type of a function, or of the return object of a
    function, the aspect value is True if
    the function is a *traversal function* and False otherwise;

  - for the type of a parameter, the aspect value is True if
    the parameter is a *traversed* parameter and False otherwise;

  - for the type of an object renaming, the aspect value is tat
    of the type of the renamed object;

 - for all other cases, the aspect value is False.

An access type (named or anonymous) whose Ownership aspect is False
is not in |SPARK|.

A name denoting an object is classified as either a *static name*,
a *dynamic name*, or neither. The following are static names:

  - a name that statically denotes an object (see 4.9);

  - a selected component with prefix being a static name;

  - a dereference (implicit or explicit), with prefix being a static
    name denoting an object of an access type with Ownership aspect True;

  - a name that denotes an object renaming declaration, if the
    object_name denoting the renamed entity is a static name.

 Any other name that denotes an object, other than an aggregate or the
 result of a non-traversal function call (or part thereof), is a dynamic
 name. [TBD: rename of agg/call; agg/call operands for type conversions,
 qualified expressions, parenthesized expressions].

 A static or dynamic name has a *root object* defined as follows:
  - if the name is a component_selection, an indexed_component, a slice,
    or a dereference (implicit or explicit)
    then it is the root object of the prefix of the name;

  - if the name denotes a call on a traversal function,
    then it is the root object of the name denoting the actual
    traversed parameter;

  - if the name denotes an object renaming, the root object is the
    root object of the renamed name.

  - otherwise, the name statically denotes an object and the root
    object is the statically denoted object.

Two names with the same root object are said to *statically overlap*
if one is a static name and the other is, or has a prefix that is,
a static name that denotes the same object as the first name.

A static name that denotes a managed object can be in one of the
following ownership states: Unrestricted, Observed, or Borrowed, or Moved.
[TBD: Instead of nulling out the RHS of an assignment, we introduce a
new state (i.e., Moved) and the RHS goes into that state. Right?
Do Moved and Borrowed need to be distinct states?]

A given name may take on different states at different points in the
program. For example, within a block_statement which declares an observer
(observers have not been defined yet), a name might have a state of Observed
while having a state of Unrestricted immediately before and immediately
after the block_statement. This is a compile-time notion, but there is a
corresponding runtime notion; at a given
point during the execution of a program, a given object may be in the
Unrestricted, Observed, Borrowed, or Moved states (as determined by rules that
have not yet been discussed). If (at compile-time) a name
is in some state at some point in a program, then (at run-time) the
named object will be in the corresponding state when execution reaches
the given point in the program.

In the Unrestricted state, no additional restrictions are imposed on the
use of the name. In particular, if the name denotes an owning access object
of an access-to-variable type then a deference of the name provides a
variable view.

In the Observed state, the name provides a constant view (even if the
named object is a variable). If it denotes an owning access object then
a dereference of the name provides a constant view [Redundant: , even if the object
is of an access-to-variable type].

In the Moved or Borrowed states, the name is unusable for either reading or
writing.

A dynamic name that denotes a managed object may also be in the
Observed, Borrowed, or Moved states (although not in the Unrestricted state),
but there is also a another possibility: a dynamic name's
ownership state may be Dynamic. [Expository: This indicates that
the value of the corresponding state at run-time is not known
at compile-time, so that run-time checks may be necessary
to maintain ownership-related invariants in some cases.]

A static name that denotes a managed object has a default ownership state
(described below).
Certain constructs (described below) are said to *observe* or
*borrow* the value of a managed object; these may change the ownership
state (to Observed or Borrowed, respectively) of a name within a certain
portion of the program text (described below).
Outside of any such region, the ownership state of
a static name that denotes a managed object is its default ownership state.

The ownership state of a dynamic name that denotes a managed object
is determined as follows:

  At any point in the program text, if a name (static or dynamic) that
  denotes a managed object has a prefix that is in the Observed or Borrowed
  state then that name is also in the Observed or Borrowed state
  (respectively). If a dynamic name that denotes a managed object is not in
  the Observed or Borrowed state because of this rule, then it is in the
  Dynamic ownership state.

The default ownership state of an unprefixed static name that denotes a
managed object is determined as follows:

  - If the name denotes a constant other than an In-mode parameter of an
    owning [TBD: access-to-variable?] type, then its default ownership
    state is Observed;

  - Otherwise, its default ownership state is Unrestricted.

[Expository: For owning access-to-variable types, a dereference of a constant
owning object usually provides a constant view of the designated
object. This is because a component of a constant is itself a constant
and a dereference of a subcomponent is treated, for purposes of
flow analysis, like a subcomponent. In-mode parameters
(but not subcomponents thereof, and not parameters of functions)
are an exception to this.]
[TBD: Do we want an aspect to distinguish In-mode parameters where this
special treatment is required from those which do not? Treating elementary
and composite parameters differently in this way seems like it will
annoy users.]

The default ownership state of a prefixed static name that denotes a
managed object is that of its prefix.

The following operations *observe* a name that denotes a managed object
and identify a corresponding *observer*:

  - An assignment operation that is used to initialize an object of an
    anonymous access-to-constant type, where this target object (the observer)
    is a stand-alone object, or a formal parameter or generic formal object
    of mode in. In this case, the source expression of the assignment
    shall be either a name denoting an object with Ownership True or
    a call on a traversal function that returns an object of an
    anonymous access-to-constant type. In the former case, the name
    being observed denotes the source of the assignment; in the latter
    case the name being observed denotes the actual traversed parameter.
    The initialized object is the observer.

  - An assignment operation that is used to initialize a constant object
    (including a generic formal object of mode in) of a composite type
    with Ownership aspect True. The name being observed denotes the
    source of the assignment. The initialized object is the observer.

  - A call where an actual parameter is a name denoting a managed object,
    and the corresponding formal parameter is of mode In and composite
    or aliased. The name being observed denotes the actual parameter.
    The formal parameter is the observer.

Such an operation is called an *obeserving operation*.

In the region of program text beween the point where a name denoting a
managed object is observed and the end of the scope of the observer, the
ownership state of the name is Observed. While a name that denotes a managed
object is in the Observed state it provides a constant view
[Redundant: , even if the name denotes a variable].

At the point where a static name that denotes a managed object is observed,
every static name that denotes the same managed object, or that has such
a static name as a prefix, is observed.

The following operations *borrow* a name that denotes a managed object
and identify a corresponding *borrower*:

  - An assignment operation that is used to initialize an owning access object,
    where this target object (the borrower) is a stand-alone variable of an
    anonymous access-to-variable type, or a constant (including a formal
    parameter or generic formal object of mode in) of a (named or anonymous)
    access-to-variable type.

    If the source of the assignment is a call on a traversal function that
    returns an object of an anonymous access-to-variable type then the name
    being borrowed denotes the actual traversed parameter. Otherwise the
    name being borrowed denotes the source of the assignment.

  - A call (or instantiation) where the (borrowed) name denotes an actual
    parameter that is a managed object other than an owning access object,
    and the formal parameter (the borrower) is of mode out or in out (or
    the generic formal object is of mode in out).

  - An object renaming where the (borrowed) name is the object_name denoting
    the renamed object. In this case, the renamed object shall not be in the
    observed or borrowed state. The newly declared name is the borrower.

    At the point (both statically in the program text and dynamically in the
    execution of the program)

Such an operation is called a *borrowing operation*.

In the region of program text beween the point where a name denoting a
managed object is borrowed and the end of the scope of the borrower, the
state of the name is Borrowed except for nested scopes wherein the
introduction of an observer changes the state to Observed.
While a name that denotes a managed object is in the Borrowed state it
provides a constant view [Redundant: , even if the name denotes a variable].
Furthermore, the only permitted read of a managed object in the Borrowed
state is the introduction of a new observer of the object. Within the
scope of such a new observer any director or indirect borrower
[TBD: define direct/indirect borrower? Does it need to be stated explicitly
that a borrower of a borrower is an indirect borrower and similarly for
observers?] of the original name similarly enters the observed state and
provides only a constant view.

At the point where a static name that denotes a managed object is borrowed,
every static name that denotes the same managed object, or that has such
a static name as a prefix, is borrowed.

The following operations are said to be *move* operations:
  - An assignment operation, where the target is a variable or return object
    (see Ada RM 6.5) having some part that is of a named type with Ownership
    aspect True, including an Out-mode or In-Out-mode formal parameter of an
    owning access type. [Redundant: This includes all assignments to or from
    such a formal parameter: copy-in before the call, copy-back after the
    call, and any assignments to the formal parameter during the call.]
    [TBD: any issues here with class-wide assignment? Probably not - no
    worse than having a component of a generic formal type with respect to
    statically identifying the "having some part" property mentioned above.]

  - An assignment operation where the target is part of an aggregate, and is
    of a named type with Ownership aspect True.

[Redundant: Passing a parameter by reference is not a move operation.]

A move operation results in a transfer of ownership. The state of
the source object of the assignment operation becomes Moved and
remains in this state until the object is assigned another value.
[TBD: this "remains in this state" wording seems like hand-waving. Is it ok?
What rules prevent, for example, leaving a global variable in a Moved state?]
[Roughly speaking, any access-valued parts of an object in the Moved state
can be thought of as being "poisoned"; such a poisoned object is treated
analogously to an uninitialized scalar object in the sense that various rules
statically prevent the reading of such a value. Thus, an assignment like::

   Pointer_1 : Some_Access_Type := new Designated_Type'(...);
   Pointer_2 : Some_Access_Type := Pointer_1;

does not violate the "single owner" rule because the move operation
poisons Pointer_1, leaving Pointer_2 as the unique owner of the
allocated object.]
[TBD: Does poisoning occur if the RHS is known to be null? Presumably yes.
For example, given::

   X : Linked_List_Node := (Data => 123, Link => null);
   Y : Linked_List_Node := X;

is X.Link poisoned by the assignment to Y?]

Two names are said to be *potential aliases* when:

  - both names statically denote the same entity [Redundant: , which
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

[TBD: Given the declaration "S : String (1 .. 3);", it seems wrong that
The names "S" and "S(1)" are not potentially aliases, but the names
"S(1..3)" and "S(1)" are potential aliases. It seems like the latter pair
should not be potential aliases. Perhaps we want to eliminate the
slice/indexed case from the preceding list and then, in the next item,
replace "is neither a slice nor an indexed component" with "is not a slice"]

[Expository: In cases described later, checks are performed at
runtime to ensure that the states of potentially overlapping
names are consistent.]

Two names N1 and N2 are said to *potentially overlap* if
  - some prefix of N1 is a potential alias of N2 (or vice versa); or

  - N1 is a call on a traversal function and the actual traversed
    parameter of the call potentially overlaps N2 (or vice versa).

The prefix and the name that are potential aliases are called the
*potentially aliased parts* of the potentially overlapping names.

An operation that occurs within an expression or simple statement is
said to *occur strictly before* a second such operation if:

  - The first occurs within an expression that is an operand of the second; or

  - The first occurs within the left operand of a short-circuit control form,
    and the second occurs within the right operand of the same
    short-circuit control form; or

  - The first occurs within the condition or selecting_expression of a
    conditional_expression, and the second occurs within a
    dependent_expression of the same conditional_expression; or

   - The first operation occurs strictly before some other operation,
     that in turn occurs strictly before the second.

The following attribute is defined for an object X of a named non-limited type
T:

X’Copy

   [Expository: X'Copy yields a "deep" copy of X, allocating copies of
   any allocated objects that are reachable from X.]

   The evaluation of X’Copy yields an anonymous constant object initialized
   by assignment from X in the same way as X'Old (see Ada RM 6.1.1) except
   that for any part of X that is of an owning access type T and whose value
   is not null, the corresponding part of X'Copy is initialized as follows:

     - If the designated type of T has an immutably limited part, then
       Program_Error is raised.

     - Otherwise, the initial value is the result of evaluating an
       an initialized allocator of the given access type whose
       initial value is a Copy attribute_reference whose prefix is
       a dereference of that non-null value.
       [For example, if X.C is of an owning access type and has a
       non-null value, then X'Copy.C will equal the result of evaluating
       T'(new Designated_Type'(X.C.all'Copy))].

   For the purposes of other language rules (e.g., for the accessibility
   level of X'Copy), X’Copy is equivalent to a call on a function that
   observes its formal parameter with X as the actual parameter.

   [TBD: We say "has an immutably limited part" because we want to ignore
   limitedness in the case of a type which has a limited view but isn't
   "really" limited. Is this the best way to express this?
   Would some other wording better clarify the status of something like::

      package Pkg is
        type T is limited private;
      private
        type T is new Integer;
      end Pkg;
      type T_Ref is access Pkg.T with Ownership;
      type Vec is array (1 .. 10) of T_Ref;
      X : Vec := ...;
      Y : Vec := X'Copy; -- succeeds; P_E is not raised

   ?]
   [TBD: Do we want to replace the runtime check with a post-compilation
   check? It can't be a compile-time check (even if we are enforcing
   legality rules in expanded instance bodies) because of limited withs
   and Taft-amendment types, but it could be a post-compilation (i.e.,
   bind-time) check. This check would be slightly more conservative than
   the runtime check in cases involving variant parts and zero-length arrays,
   but that seems like a good thing. The definition of the post-compilation
   check might involve a definition something like

     A type T2 is said to be *reachable* from a type T1 if

       - T1 has a part of type T2; or

       - T1 has a part of an owning access type and T2 is reachable from
         the designated type of that access type.

   and then a rule that X'Copy is illegal if an immutably limited type is
   reachable from the type of X. Or something like that - strictly speaking
   the use of "immutably limited" rule might not be quite right because
   we want this rule to ignore privacy like a dynamic semantics rule.]

.. centered:: **Legality Rules**

[TBD: acknowledge in an informal note that some legality rules have already
been given as part of the preceding definitions?]

..  _tu-access_types-01:

At the point where an object of an owning access type is finalized [redundant:
(which may occur either when the object is the target of an assignment
operation or upon exiting the scope in which the object is declared)], the
object's state shall be Moved or Unrestricted. In the case where it is
Unrestricted, a verification condition is generated to ensure that value of
object is null.
[Redundant: This rule is needed to prevent storage leaks.]

.. _tu-access_types-02:

At the point of a move operation, the source object's state shall be
Unrestricted.

.. _tu-access_types-03:

If the target of an assignment operation is an object of an anonymous
access-to-object type with Ownership True (including a parameter), then
the source shall be neither an allocator nor a non-traversal function call.
[Redundant: This rule is needed to avoid storage leaks and to help ensure
that every allocator is of a named access type.]

.. _tu-access_types-04:

A return statement that applies to a traversal function that has an
anonymous access-to-constant (respectively, access-to-variable) result type,
shall return an access object denoted by a direct or indirect observer
(respectively, borrower) of the traversed parameter. [Expository:
Roughly speaking, such a traversal function always yields a result
which is reachable from the traversed parameter.]
[TBD: presumably such a function is also allowed to return null?]

.. _tu-access_types-05:

If the prefix of a name is of a type with Ownership aspect True, then the
prefix shall denote neither a non-traversal function call, an aggregate,
an allocator, nor a qualified expression or type conversion whose
operand is would be forbidden as a prefix by this rule.
[TBD: bite the bullet and introduce a new term here?]

.. _tu-access_types-06:

If an Access or Unchecked_Access attribute reference is of a type
with the Ownership aspect True, then the prefix shall denote a managed object,
and the attribute value shall be directly used either to initialize a
stand-alone object of an anonymous access type, or as an actual parameter
corresponding to an In-mode formal parameter of an anonymous access type.
[Redundant: This is observing the prefix if the anonymous access
type is access-to-constant, and borrowing otherwise.]
[TBD: confirm that the preceding sentence is redundant; we are not augmenting
definitions of "observing" and "borrowing" here.]

.. _tu-access_types-07:

If the root of the name of the managed object denotes an object whose scope
includes the visible part of a package, then a declaration that observes or
borrows a managed object shall not occur within the private part or body of the
package, nor withing a private descendant of a package, unless the
accessibility level of the declaration is statically deeper than that of the
package.

.. _tu-access_types-08:

In the case of a [Redundant: (explicit or implicit)] type conversion, the
Ownership aspects of the operand type and of the target type shall be the
same. In the case of a non-overridden inherited subprogram, the Ownership
aspects of the inheriting type and of the corresponding ancestor type
shall be the same. In the case of a primitive operation of
a tagged type that overrides an inherited operation, the Ownership aspects of
the type and of the ancestor type from which the overridden operation
was inherited shall be the same.
[TBD: somehow relax this if Extensions_Visible => False?]

.. _tu-access_types-09:

For an assignment statement where the target is a stand-alone object of an
anonymous access-to-object type with Ownership aspect True:

  - If the type of the target is an anonymous access-to-variable type
    (an owning access type), the source shall be an owning access object
    denoted by a name that is not in the observed or borrowed state, and
    whose root object is the target object itself;

  -If the type of the target is an anonymous access-to-constant type
   (an observing access type), the source shall be an owning access object
   denoted by a name that is in the observed state, and whose root object
   is also in the observed state and not declared at a statically deeper
   accessibility level than that of the target object.


.. _tu-access_types-10:

If state of a name that denotes a managed object is observed, then the
name shall neither be moved nor borrowed and shall not be used as the
target of an assignment.

.. _tu-access_types-11:

If the state of a name that denotes a managed object is borrowed, the name
shall not be moved, borrowed, or assigned, and shall not be used as a primary,
as a prefix, or as an actual parameter except as part of being observed;
furthermore, any existing borrowers (direct or indirect) of the name become
observers, providing only a constant view.

.. _tu-access_types-12:

If the source of a "move" is a name that denotes an object with Ownership
aspect True, other than a function call, the name shall be a variable
[Redundant: that is not in the observed or borrowed state]; furthermore,
there shall be no name that statically overlaps this name
that is in the observed or borrowed state;
[TBD: as discussed earlier, what does it mean say "there shall be no name"?
what is the set of names to which this check is applied? This is too fuzzy.]

.. _tu-access_types-13:

At the point of a call, any name that denotes a managed object that is a global
output of the callee (i.e., an output other than a parameter of the callee
or a function result) shall not be in the observed or borrowed state.
Similarly, any name that denotes a managed object that is a global input
of the callee  shall not be in the borrowed state.
[TBD: Again, what is the set of names to which this check is applied?
This seems like a wrong way to express this idea. Perhaps we could talk
about the state of declarations in addition to that of names. Then we could
say something here like

    At the point of a call, the declaration of every global output of the
    call shall not be in the borrowed state.]

.. _tu-access_types-14:

The name of a parameter in a call shall not potentially overlap a global
output of the callee.
The name of a parameter in a call shall not potentially overlap a global
input of the callee if the corresponding formal parameter is an output
of the callee.
[TBD: Is this rule redundant? I think so.]
[TBD: In the original proposal, we had static checks for guaranteed
overlap and runtime checks for potential overlap. Because SPARK globals
are always top-level objects (as opposed to subcomponents), this
distinction has no value. Static overlap = potential overlap if one of the
tested names is simply the name of a type level object.]

.. _tu-access_types-15:

Statically overlapping parts of a single variable shall not be passed as
two actual parameters to a single call unless

  - the call is a function call; or
  - both corresponding formal parameters are of mode **in** and both
    formal parameter types are composite; or
  - at least one of the two parameter types is scalar.

[TBD: Say "Potentially overlapping" instead of "Statically overlapping"
here and then eliminate the corresponding dynamic semantics rule? This would
be more conservative but it would eliminate the need for VCs having to
do with overlapping.]

.. centered:: **Dynamic Semantics**

.. _tu-access_types-16:

[For managed objects denoted by a dynamic name, checks are used to ensure that
no other name that is a potential alias is in a conflicting state.]

For a dynamic name D1 that is in a Dynamic ownership state, if an operation
(e.g., an observing operation, a borrowing operation, a move operation, or a
call) requires that, were D1 a static, it not be in an observed (or borrowed)
state, then for every other dynamic name D2 that is in the observed (or
borrowed) state and potentially overlaps with D1, a check is made at the
start of the operation that the potentially aliased parts of the names do
not in fact denote overlapping parts of the same object.  If this check fails,
Program_Error is raised.

[TBD: It would be nice to explicitly list the operations in question, but
the current treatment is ok at least for now. But it seems very unclear
precisely what D2 objects are being checked. I think it would help if we
described a possible implementation model. As it stands, this description
seems unacceptably vague.]

.. _tu-access_types-17:

If potentially overlapping parts of a single variable are passed as
two actual parameters to a single call and

  - the call is not a function call; and

  - corresponding formal parameters are of mode **in** and both
    formal parameter types are composite; and

  - neither of the two parameter types is a scalar type

then a check is performed before the call that the actual
parameters do not overlap; Program_Error is raised if this check fails.

.. _etu-access_types:

Declarative Parts
-----------------

No extensions or restrictions.
