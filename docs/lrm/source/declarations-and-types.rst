Declarations and Types
======================

No extensions or restrictions.

Declarations
------------

.. index:: entity, view of an entity

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

.. index:: define full default initialization

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
    *Boolean_*\ ``expression`` and whose full view is not in |SPARK|; or

  * a private type whose full view is in |SPARK| and defines full default
    initialization.

[The discriminants of a discriminated type play no role in determining
whether the type defines full default initialization.]


Types and Subtypes
------------------

No extensions or restrictions.


Type Declarations
~~~~~~~~~~~~~~~~~

No extensions or restrictions.


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

.. index:: expression with a variable input

An *expression with a variable input* reads a variable or calls a
function which (directly or indirectly) reads a variable.

.. container:: heading

   Legality Rules

1. [A ``constraint``, excluding the ``range`` of a
   ``loop_parameter_specification``, shall not be defined using an
   expression with a variable input;
   see :ref:`Expressions` for the statement of this rule.]



Classification of Operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No restrictions or extensions.

.. index:: subtype predicate

Subtype Predicates
~~~~~~~~~~~~~~~~~~

Static predicates and dynamic predicates are both in
|SPARK|, but subject to some restrictions.

.. container:: heading

   Legality Rules

1. [A Dynamic_Predicate expression shall not have a variable input;
   see :ref:`Expressions` for the statement of this rule.]

.. index:: verification condition; for Dynamic_Predicate

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
  an extension aggregate, or a delta aggregate.
  These are assignment operations but not assignment statements.]

.. index:: effectively volatile for reading; exclusion of predicates

3. A Static_Predicate or Dynamic_Predicate shall not apply to a subtype of a
   type that is effectively volatile for reading.

.. container:: heading

   Verification Rules

.. index:: termination; of Dynamic_Predicate

4. A Dynamic_Predicate expression shall always terminate.


Objects and Named Numbers
-------------------------

Object Declarations
~~~~~~~~~~~~~~~~~~~

.. index:: Constant_After_Elaboration

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
(see section :ref:`Tasks and Synchronization`).]

.. index:: constant with variable inputs

A stand-alone constant is a *constant with variable inputs* if its
initialization expression depends on:

  * A variable or parameter; or

  * Another *constant with variable inputs*

Otherwise, a stand-alone constant is a *constant without variable inputs*.

.. container:: heading

   Legality Rules


1. [The borrowed name of the expression of an object declaration defining a
   borrowing operation shall not have a variable input, except for a single
   occurrence of the root object of the expression;
   see :ref:`Expressions` for the statement of this rule.]

.. container:: heading

   Verification Rules


2. Constants without variable inputs shall not be denoted in Global,
   Depends, Initializes or Refined_State aspect specifications.
   [Two elaborations of such a constant declaration will always
   yield equal initialization expression values.]


.. container:: heading

   Examples

.. code-block:: ada

   A : constant Integer := 12;
   --  No variable inputs

   B : constant Integer := F (12, A);
   --  No variable inputs if and only if F is a function without global inputs
   --  (although it could have global proof inputs)

   C : constant Integer := Param + Var;
   --  Constant with variable inputs


Number Declarations
~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Derived Types and Classes
-------------------------

The following rules apply to derived types in |SPARK|.

.. container:: heading

   Legality Rules


1. A private type that is not visibly tagged but whose full view is tagged
   cannot be derived.

[The rationale for this rule is that, otherwise, given that visible operations
on this type cannot have class-wide preconditions and postconditions, it is
impossible to check the verification rules associated to overridding operations
on the derived type.]


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

Real types
~~~~~~~~~~

Non-static expressions of type *root_real* are not supported [because the
accuracy of their run-time evaluation depends on the implementation].

Array Types
-----------

No extensions or restrictions.


Discriminants
-------------

The following rules apply to discriminants in |SPARK|.

.. container:: heading

   Legality Rules


1. The type of a ``discriminant_specification`` shall be discrete.


2. A ``discriminant_specification`` shall not occur as part of a
   derived type declaration.


3. [The ``default_expression`` of a ``discriminant_specification``
   shall not have a variable input;
   see :ref:`Expressions` for the statement of this rule.]


Record Types
------------

Default initialization expressions must not have variable inputs in |SPARK|.

.. container:: heading

   Legality Rules


1. [The ``default_expression`` of a ``component_declaration`` shall not
   have any variable inputs, nor shall it contain a name denoting
   the current instance of the enclosing type;
   see :ref:`Expressions` for the statement of this rule.]


[The rule in this section applies to any ``component_declaration``; this
includes the case of a ``component_declaration`` which is a
``protected_element_declaration``. In other words, this rule also applies to
components of a protected type.]

Tagged Types and Type Extensions
--------------------------------

.. container:: heading

   Legality Rules


1. No construct shall introduce a semantic dependence on the Ada language
   defined package Ada.Tags.  [See Ada RM 10.1.1 for the definition of semantic
   dependence.  This rule implies, among other things, that any use of the Tag
   attribute is not in |SPARK|.]


2. The identifier External_Tag shall not be used as an
   ``attribute_designator``.



Type Extensions
~~~~~~~~~~~~~~~

.. container:: heading

   Legality Rules


1. A type extension shall not be declared within a subprogram body, block
   statement, or generic body which does not also enclose the declaration of
   each of its ancestor types.



Dispatching Operations of Tagged Types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Abstract Types and Subprograms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Interface Types
~~~~~~~~~~~~~~~

No extensions or restrictions.

.. index:: access type, ownership

Access Types
------------

In order to reduce the complexity associated with the specification
and verification of a program's behavior in the face of pointer-related
aliasing, anonymous access-to-constant types and (named or anonymous)
access-to-variable types are subjected to an *ownership policy*.

Restrictions are imposed on the use of these access objects in order
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
indices instead of access values), but they may be harder to reason about.

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

The rules which accomplish all of this are described below.

.. container:: heading

   Static Semantics

Only the following (named or anonymous) access types are in |SPARK|:

- a named access-to-object type,

- the anonymous type of a stand-alone object (excluding a generic formal **in**
  mode object) which is not Part_Of a protected object,

- an anonymous type occurring as a parameter type, or as a function result type
  of a traversal function (defined below), or

- an access-to-subprogram type associated with the "Ada" or "C" calling
  convention.

[Redundant: For example, access discriminants and access-to-subprogram types
with the "protected" calling convention are not in |SPARK|.]

User-defined storage pools are not in |SPARK|; more specifically, the package
System.Storage_Pools, Storage_Pool aspect specifications, and the Storage_Pool
attribute are not in |SPARK|.

In the case of a constant object of an access-to-variable type where the
object is not a stand-alone object and not a formal parameter (e.g.,
if the object is a subcomponent of an enclosing object or is designated
by an access value), a dereference of the object provides a constant
view of the designated object [redundant: , despite the fact that the
object is of an access-to-variable type. This is
because a subcomponent of a constant is itself a constant and a dereference
of a subcomponent is treated, for purposes of analysis, like a
subcomponent].

.. index:: traversal function
           observing traversal function
           borrowing traversal function

A function is said to be a *traversal function* if the result type of the
function is an anonymous access-to-object type and the function has at least one
formal parameter. The traversal function is said to be
an *observing traversal function* if the result type of the function is an
anonymous access-to-constant type, and a *borrowing traversal function* if the
result type of the function is an anonymous access-to-variable type. The first
parameter of the function is called the *traversed* parameter. [Redundant: We
will see later that if a traversal function yields a non-null result, then that
result is "reachable" from the traversed parameter in the sense that it could
be obtained from the traversed parameter by some sequence of component
selections, array indexing operations, and access value dereferences.]

.. index:: root object

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

A *path* is either:

- a stand-alone object or a formal parameter,

- a component_selection or dereference whose prefix is a path,

- a slice whose discrete range is made of two literals and whose prefix is
  a path which is not a slice, or

- an indexed_component whose expressions are literals and whose prefix is a
  path which is not a slice.

The *path extracted from a name* whose root object is a stand-alone object or a
formal parameter and which does not contain any traversal function calls is
defined as follows:

- if the name is a dereference (implicit or explicit), then it is a
  dereference of the path extracted from the prefix of the name;

- if the name is a component_selection, then it is a component_selection
  of the same component on the path extracted from the prefix of the name;

- if the name is an indexed_component, then it is an indexed_component with
  the literals that each index expression evalutates to, on the path extracted
  from the prefix of the name, or, if this path is a slice, the prefix of this
  slice;

- if the name is a slice, then it is a slice whose discrete range is
  constructed with the literals that the discrete range of the name
  evalutates to, on the path extracted from the prefix of the name, or, if this
  path is a slice, the prefix of this slice;

- if the name is a qualified_expression or a type conversion, then it is the
  path extracted from the path of the expression of the name;

- if the name denotes an object renaming, then it is the path extracted from
  the renamed name;

- otherwise, the name is a stand-alone object or formal parameter and the
  path is this object.

If a path P1 has another path P2 as a prefix, then P1 is an *extension* of
P2.

.. index:: potential aliases

Two names are said to be *potential aliases* when their root object is
a stand-alone object or a formal parameter, they do not contain any traversal
function calls, and either:

 - they have the same extracted path,
 - the extracted path of one of the names is a slice and the extracted
   path of the other is an indexed_component whose index is in the
   discrete range of the slice, or
 - the extracted path of one of the names is a slice and the extracted
   path of the other is another slice and the discrete range of both slices
   overlap.

.. index:: potentially overlap

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

.. index:: reachable part

An object O1 is said to be a *reachable part* of an object O2 if:

- O1 is a part of O2; or
- O1 is a reachable part of the object designated by (the value of) an
  access-valued part of O2.

A path is said to denote a reachable part of an object, if it is the
path extracted from a name which denotes this reachable part.

A path can be marked by one of the following
*ownership markers* for this object: Persistent, Observed,
Borrowed, or Moved.
Due to aliasing, there can be several paths denoting a given object, with
different associated markers.

A given path cannot have more than one marker at a given program point,
but it may have different markers at different points in the program.
For example, within a block_statement which declares a borrower
(borrowers have not been defined yet), the path extracted from the
borrowed name will be marked as Borrowed, while it will have no
marks immediately before and immediately after the
block_statement. [Redundant: This is a compile-time notion; no
mapping of any sort is maintained at runtime.]

When a path P is marked as Observed or Persistent, then all names whose
extracted path is an extension of P provide a constant view of their denoted
object and its reachable parts (even if the root object is a variable).
If P is marked as Persistent, then it will never be possible to
modify its denoted object and its reachable parts again in the program, and
it is OK to lose track of the owner of its potential access-to-variable parts.

When a path P is marked as Moved, then names whose extracted path is an
extension of P cannot be used to read or modify the objected denoted by P or its
reachable parts (although names whose extracted path is a strict prefix of P
can be assigned to).

When a path P is marked as Borrowed, then names whose extracted path is an
extension of P cannot be used to read or modify the objected denoted by P or its
reachable parts, and names whose extracted path is a strict prefix of P
cannot be assigned to.

A path P is said to have *unrestricted prefixes* if all prefixes of P are
unmarked.

A path P is said to be *unrestricted*, if P has unrestricted prefixes and no
extensions of P are marked as either Observed, Borrowed,
or Moved [A path P can be unrestricted even if there are extensions of P
which are marked as Persistent].

A path P said to be *observable*, if no prefixes of P and no extensions P
are marked as either Borrowed or Moved.

The ownership rules presented in this section ensure that:

- [single-ownership] if a given object O is denoted by two distinct paths
  P1 and P2 at a given program point and P1 is unrestricted, then P2 is not
  observable.

Together with the fact that:

- [ownership-write] O can only be written from a name with an unrestricted
  extracted path and
- [ownership-read] O can only be read from a name with an observable
  extracted path,

these are enough to ensure absence of harmful aliasing.


.. index:: ownership; move
           ownership; observe
           ownership; borrow


Unless otherwise specified, all paths are initially unmarked except:

- a root object R is marked as Observed if R is a constant and does not have
  an access-to-variable type, and
- a dereference is marked as Persistent if its prefix is a path denoting an
  object of an access-to-constant type.

Certain constructs (described below) are said to *observe*, *borrow*,
or *move* a path; these may change the
ownership markers (to Observed, Borrowed, or Moved respectively) of
a path within a certain portion of the program text
(described below). In the first two cases (i.e. observing and borrowing),
the ownership marker of the path
reverts to its previous value at the end of this region of text.
The markers are considered to be reverted after the finalization
of the borrower/observer but before the
finalization of the root of the borrowed or observed paths if
they are declared in the same memory region.

If the root object of a name is a stand-alone object or a formal
parameter, then the *known extracted path* of that name is either:

- the path extracted from the name, if it does not include any traversal
  function calls from the root object,
- the path extracted from the first parameter to the innermost traversal
  function call within the name otherwise.

[Redundant: The root of the known extracted path of a name is always
the root object of the name.]

A *markable expression* is either a name whose root object is a
stand-alone object or a formal parameter or a reference to the Access
attribute whose prefix is a name whose root object is a stand-alone
object or a formal parameter.

By extension, the root object and known extracted path of
a markable expression are defined as the root object and known
extracted path of the prefix for a reference to the Access
attribute and of the name otherwise.

The following operations *observe* a path and identify a corresponding
*observer*:

- An assignment operation that is used to initialize an access object,
  where this target object (the observer) is a stand-alone variable of an
  anonymous access-to-constant type, or a constant (including a formal
  parameter of a procedure or generic formal object of mode **in**) of an
  anonymous access-to-constant type.

  The source expression of the assignment shall be a markable expression.
  The known extracted path of the source of the assignment is
  observed by the assignment.

- Inside the body of a borrowing traversal function, an assignment operation
  that is used to initialize an access object, where this target object (the
  observer) is a stand-alone object of an anonymous access-to-variable type,
  and the source expression of the assignment is a markable expression whose
  root object is either the traversed parameter for the
  traversal function or another object of an access-to-variable type
  initialized as an observer.
  The known extracted path of the source of the assignment is
  observed by the assignment.

Such an operation is called an *observing operation*.

In the region of program text between the point where a path
is observed and the end of the scope of the observer, the path is marked as
Observed.

The following operations *borrow* a path
and identify a corresponding *borrower*:

- An assignment operation that is used to initialize an access object, where
  this target object (the borrower) is a stand-alone variable or constant of an
  anonymous access-to-variable type, unless this assignment is
  already an *observing operation* inside the body of a borrowing traversal
  function, per the rules defining *observe* above.

  The source expression of the assignment shall be a markable expression.
  The known extracted path of the source of the assignment is
  borrowed by the assignment.

Such an operation is called a *borrowing operation*.

In the region of program text between the point where a path
is borrowed and the end of the scope of the borrower, the
path is marked as Borrowed.

An indirect borrower of a path is defined to be a borrower either of
a borrower of the path or of an indirect borrower of the path.
A direct borrower of a markable part is just another term for a borrower of
the path, usually used together with the term "indirect borrower".
The terms "indirect observer" and "direct observer" are defined analogously.

The following operations are said to be *move* operations:

- An assignment operation, where the target is a variable, a constant, or
  return object (see Ada RM 6.5) of a type containing subcomponents of a
  named access-to-variable type. [This includes the case of an object of
  named access-to-variable type.]

[Redundant: Passing a parameter by reference is not a move operation.]

A move operation results in a transfer of ownership. The state of the paths
that are marked as Moved by the operation remain in this state until
the object is assigned another value.

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

.. container:: heading

   Legality Rules

1. At the point of a move operation, the source shall be a name which does
   not involve any traversal function calls from the root object or a reference
   to the Access attribute whose prefix is a name which does
   not involve any traversal function calls from the root object.
   In addition, if the source is a markable expression,
   the known extracted path P of the source shall be unrestricted.
   If the source is a markable expression which is not a reference
   to the Access attribute, for all extensions Q of P with no additional
   dereferences designating objects of a named access-to-variable type,
   Q.all is marked as Moved after the move operation.
   If the source is a markable expression which is a reference to the Access
   attribute, the known extracted path of it prefix is marked as Moved
   after the move operation.

2. A name whose type has subcomponents of a [named] access-to-variable type
   which is used as the target of an assignment or as an actual
   parameter of mode **out** or **in out** shall have a root object which
   is either a stand-alone object or a formal parameter, and it shall not
   involve any traversal function calls
   from this root object. In addition, if P is the path extracted from a
   name used as the target of an assignment operation or as an actual
   parameter of mode **out** in a call,

   - P shall have unrestricted prefixes,
   - there shall be no extension of P marked as Borrowed or Observed, and
   - all extensions of P marked as Moved shall contain additional dereferences.

   All paths with the target as a root are reset to their initial value after
   the operation.

   [Redundant: In the case of a call, the mark of an actual parameter of mode
   **in** or **in out** remains unchanged (although one might choose to think
   of it as being moved at the point of the call and then moved back when
   the call returns - either model yields the same results); an
   actual parameter of mode **out** becomes unrestricted.]


3. If the target of an assignment operation is an object of an anonymous
   access-to-object type (including copy-in for a parameter), then the source
   shall be a markable expression.

   [Redundant: One consequence of this rule is that every allocator is of a
   named access type.]


4. A declaration of a stand-alone object of an anonymous access type shall have
   an explicit initial value and shall occur immediately within a subprogram
   body, an entry body, or a block statement.

   [Redundant: Because such declarations cannot occur immediately within a
   package declaration or body, the associated borrowing/observing operation is
   limited by the scope of the subprogram, entry or block statement. Thus, it
   is not necessary to add rules restricting the visibility of such
   declarations.]


5. A return statement that applies to a traversal function that has an
   anonymous access-to-constant (respectively, access-to-variable) result type,
   shall return either the literal null or a markable expression whose root
   object is a direct or indirect observer (respectively, borrower) of the
   traversed parameter.
   [Redundant: Roughly speaking, a traversal function always yields either null
   or a result which is reachable from the traversed parameter.]


6. If a name whose type has subcomponents of a named access-to-variable type
   is a non-traversal function call or an allocator, it shall only occur
   in an acceptable context, namely:

   - As the initial expression of an object declaration which does not
     occur in a declare expression,

   - As the source of an assignment,

   - As the return value of a return statement,

   - As the expression of a type conversion or qualified expression itself
     occurring in an acceptable context,

   - As an aggregate itself occurring in an acceptable context, or

   - Anywhere inside a contract or an assertion.
     [While legal, such an expression inside a contract or assertion will
     leak memory. A verification rule below forbids leaking memory, leading
     to a violation on such uses. The intent is to allow the use of
     allocators and allocating functions inside contracts and assertions,
     but make sure that users are aware of the possible memory leaks if
     such contracts and assertions are executed at runtime.]


7. For an assignment statement where the target is a stand-alone object of an
   anonymous access-to-object type, the source shall be a markable expression
   whose root object is the target object itself. In addition:

   - If the type of the target is an anonymous access-to-constant type or
     if the target is a local object of a borrowing traversal function whose
     initialization is an observing operation, the known extracted path
     of the source shall be observable for the target object;

   - If the type of the target is an anonymous access-to-variable type,
     which does not fall in the case above, then the target object shall be
     unrestricted.


8. At the point of a read of an object, or of passing an object as an actual
   parameter of mode **in** or **in out**, or of a call where the object is a
   global input of the callee, if the object is a markable expression, then its
   known extracted path shall be observable.

9. At the point of a return statement, or at any other point where a call
   completes normally (e.g., the end of a procedure body), there shall be
   no paths marked as Moved with any inputs or outputs of the callee being
   returned from as a root. In the case
   of an input of the callee which is not also an output, this rule may be
   enforced at the point of the move operation (because there is no way for the
   Moved marker to be removed from the input), even in the case of a
   subprogram which never returns.

   Similarly, at the end of the elaboration of both the declaration and of the
   body of a package, there shall be no paths marked as Moved whose root
   is denoted by the name of
   an initialization_item of the package's Initializes aspect or by an input
   occuring in the input_list of such an initialization_item.

   At the end of the scope of an object of an anonymous access-to-variable
   type, or at any other point where the scope of an object of an anonymous
   access-to-variable type is exited normally, there shall be no paths marked
   as Moved with the object as a root.


10. For a borrowing operation, the borrowed path shall be unrestricted.


11. At the point of a call, no paths with any global output of the callee
    (i.e., an output other than a parameter of the
    callee or a function result) as a root shall be marked as
    Borrowed or Observed, and all such paths which are marked as Moved shall
    contain dereferences.


12. The prefix of an Old or Loop_Entry attribute reference shall not be of an
    anonymous access-to-object type nor of a type with subcomponents of a named
    access-to-variable type unless the prefix is a call to a non-traversal
    function.


13. A derived tagged type shall not have a component of a named
    access-to-variable type.


14. If the designated type of a named nonderived access type is incomplete
    at the point of the access type's declaration then the incomplete
    type declaration and its completion shall occur in the same
    declaration list. [This implies that the incomplete type shall not be
    declared in the limited view of a package, and that if it is declared
    in the private part of a package then its completion shall also occur
    in that private part.]


15. A path rooted at an effectively volatile object shall not be
    moved, borrowed, or observed.
    [This rule is meant to avoid introducing aliases
    between volatile variables used by another task or thread. Borrowers can
    also break the invariant on the borrowed object for the time of the
    borrow.]

16. Objects of an anonymous access-to-object types shall not be converted
    (implicitly or explicitly) to a named access type.

17. Evaluation of equality operators, and membership tests where one or more of
    the choices are expressions, shall not include directly or indirectly calls
    to the primitive equality on access types, unless one of the operands is
    syntactically null.

18. Instances of Unchecked_Deallocation shall not have a general access type
    as a parameter.

.. container:: heading

   Verification Rules

.. index:: memory leak; for objects
           deallocation, Unchecked_Deallocation

19. When an object R which does not have an anonymous access-to-object type
    is finalized or when it is passed as an actual parameter
    of mode **out**, all extensions of the path extracted from R which denote
    an object of a pool-specific access type and
    have unrestricted prefixes shall be null.

    Similarly, at the point of a call, for each global output R of the callee
    (i.e., an output other than a parameter of the callee or a function
    result) that is not also an input, all paths rooted at R which denote
    an object of a pool-specific access type and which have unrestricted
    prefixes shall be null.

    [Redundant: This rule applies to any finalization associated with a
    call to an instance of Ada.Unchecked_Deallocation. For details, see
    the Ada RM 13.11.2 rule "Free(X), ... first performs finalization of
    the object designated by X".]

    [Redundant:This rule effectively forbids the use of allocators and
    calls to allocating functions inside contracts or assertions.]

20. Allocators and conversions from a pool-specific access type to a named
    access-to-constant type or a general access-to-variable type shall only
    occur at library level.

    In the same way, a reference to the Access attribute of a named
    access-to-object type whose prefix contains a dereference of a
    pool-specific access-type shall occur at library level.

    [Redundant: Together with the previous one, this rule disallows storage
    leaks. Without these rules, it would be possible to "lose" the last
    reference to an allocated object.]


21. When converting from a [named or anonymous] access-to-subprogram type
    to another, if the converted expression is not null,
    a verification condition is introduced to ensure that the
    precondition of the source of the conversion is implied by the
    precondition of the target of the conversion. Similarly, a verification
    condition is introduced to ensure that the postcondition of the target
    is implied by the postcondition of the converted access-to-subprogram
    expression.


Declarative Parts
-----------------

No extensions or restrictions.
