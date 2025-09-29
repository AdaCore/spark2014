Implementation Defined Annotations
==================================

This appendix lists all the uses of aspect or pragma ``Annotate`` for
|GNATprove|.  Aspect or pragma ``Annotate`` can also be used to control other
AdaCore tools. The uses of such annotations are explained in the User's Guide
of each tool.

Annotations in |GNATprove| are useful in two cases:

1. for justifying check messages using :ref:`Direct Justification with Pragma
   Annotate`, typically using a pragma rather than an aspect, as the
   justification is generally associated to a statement or declaration.

2. for influencing the generation of proof obligations, typically using an
   aspect rather than a pragma, as the annotation is generally associated to an
   entity in that case. Some of these uses can be seen in :ref:`SPARK
   Libraries` for example. Some of these annotations introduce additional
   assumptions which are not verified by the |GNATprove| tool, and thus should
   be used with care.

When the annotation is associated to an entity, both the pragma and aspect form
can be used and are equivalent, for example on a subprogram:

.. code-block:: ada

    function Func (X : T) return T
      with Annotate => (GNATprove, <annotation name>);

or

.. code-block:: ada

    function Func (X : T) return T;
    pragma Annotate (GNATprove, <annotation name>, Entity => Func);

In the following, we use the aspect form whenever possible.

.. index:: Annotate; False_Positive
           Annotate; Intentional

Annotation for Justifying Check Messages
----------------------------------------

You can use annotations of the form

.. code-block:: ada

    pragma Annotate (GNATprove, False_Positive,
                     "message to be justified", "reason");

to justify an unproved check message that cannot be proved by other means. See
the section :ref:`Direct Justification with Pragma Annotate` for more details
about this use of pragma ``Annotate``.

.. index:: Annotate; Skip_Proof; Skip_Flow_And_Proof

Annotation for Skipping Parts of the Analysis for an Entity
-----------------------------------------------------------

Subprograms, packages, tasks, entries and protected subprograms can be
annotated to skip flow analysis, and to skip generating proof obligations for
their implementation, and the implementations of all such entities defined
inside.

.. code-block:: ada

   procedure P
     with Annotate => (GNATprove, Skip_Proof);

   procedure P
     with Annotate => (GNATprove, Skip_Flow_And_Proof);

If an entity is annotated with ``Skip_Proof``, no messages related to possible
run-time errors and functional contracts are issued for this entity and any
contained entities. This is similar to specifying ``--mode=flow`` on the command
line (see :ref:`Effect of Mode on Output`), except that the effect is limited
to this entity (and enclosed entities).

If an entity is annotated with ``Skip_Flow_And_Proof``, in addition, no messages
related to global contracts, initialization and dependency relations are issues
for this entity and any contained entities. This is similar to specifying
``--mode=check-all`` on the command line, expect that the effect is limited to
this entity (and enclosed entities).

Note that the ``Skip_Proof`` annotation cannot be used if an enclosing
subprogram already has the ``Skip_Flow_And_Proof`` annotation.

.. index:: Annotate; No_Bitwise_Operations

Annotation for Handling Modular Types as Integers in All Provers
----------------------------------------------------------------

Modular types are handled as a special `bitvector` type in some provers, which
may lead to more difficult automatic proofs when such values are combined with
integers that come from signed integers in SPARK or ``Big_Integers`` from the
:ref:`SPARK Library`.

In such a case, it is possible to request that a modular type is handled like
an integer in all provers, by using annotations of the form:

.. code-block:: ada

   type T is mod 2**32
     with Annotate => (GNATprove, No_Bitwise_Operations);

or on a derived type:

.. code-block:: ada

   type T is new U
     with Annotate => (GNATprove, No_Bitwise_Operations);

This annotation is inherited by derived types. It must be specified on a type
declaration (and cannot be specified on a subtype declaration). The following
bitwise operations are not allowed on such a type: ``or``, ``and``, ``xor``,
``not``, ``Shift_Left``, ``Shift_Right``, ``Shift_Right_Arithmetic``,
``Rotate_Left``, ``Rotate_Right``.

.. index:: Annotate; No_Wrap_Around

Annotation for Overflow Checking on Modular Types
-------------------------------------------------

The standard semantics of arithmetic on modular types is that operations wrap
around, hence |GNATprove| issues no overflow checks on such operations.
You can instruct it to issue such checks (hence detecting possible wrap-around)
using annotations of the form:

.. code-block:: ada

   type T is mod 2**32
     with Annotate => (GNATprove, No_Wrap_Around);

or on a derived type:

.. code-block:: ada

   type T is new U
     with Annotate => (GNATprove, No_Wrap_Around);

This annotation is inherited by derived types. It must be specified on a type
declaration (and cannot be specified on a subtype declaration). All four binary
arithmetic operations + - * \*\* are checked for possible overflows. Division
cannot lead to overflow. Unary negation is checked for possible non-nullity of
its argument, which leads to overflow. The predecessor attribute ``'Pred`` and
successor attribute ``'Succ`` are also checked for possible overflows.

.. warning::

   Even if a type is annotated with ``No_Wrap_Arround``, no overflow checks are
   introduced for computations done at compile time in static expressions.

Annotation for Simplifying Iteration for Proof
----------------------------------------------

.. index:: Annotate; Iterable_For_Proof

The translation presented in :ref:`Aspect and Pragma Iterable`
may produce complicated proofs,
especially when verifying complex properties over sets. The |GNATprove|
annotation ``Iterable_For_Proof`` can be used to change the way ``for ... of``
quantification is translated. More precisely, it allows to provide |GNATprove|
with a `Contains` function, that will be used for quantification. For example,
on our sets, we could write:

.. code-block:: ada

  function Mem (S : Set; E : Element_Type) return Boolean with
    Annotate => (GNATprove, Iterable_For_Proof, "Contains");

With this annotation, the postcondition of ``Intersection`` is translated in a
simpler way, using logic quantification directly over elements (not valid Ada syntax):

::

  (for all E : Element_Type =>
       (if Mem (Intersection'Result, E) then Mem (S1, E) and Mem (S2, E)))
  and (for all E : Element_Type =>
       (if Mem (S1, E) then
              (if Mem (S2, E) then Mem (Intersection'Result, E))))

Note that care should be taken to provide an appropriate function contains,
which returns true if and only if the element ``E`` is present in ``S``. This
assumption will not be verified by |GNATprove|.

The annotation ``Iterable_For_Proof`` can also be used in another case.
Operations over complex data structures are sometimes specified using operations
over a simpler model type. In this case, it may be more appropriate to translate
``for ... of`` quantification as quantification over the model's cursors. As an
example, let us consider a package of linked lists that is specified using a
sequence that allows accessing the element stored at each position:

.. code-block:: ada

  package Lists with SPARK_Mode is

   type Sequence is private with
     Ghost,
     Iterable => (...,
                  Element     => Get);
   function Length (M : Sequence) return Natural with Ghost;
   function Get (M : Sequence; P : Positive) return Element_Type with
     Ghost,
     Pre => P <= Length (M);

   type Cursor is private;
   type List is private with
     Iterable => (...,
                  Element     => Element);

   function Position (L : List; C : Cursor) return Positive with Ghost;
   function Model (L : List) return Sequence with
     Ghost,
     Post => (for all I in 1 .. Length (Model'Result) =>
                  (for some C in L => Position (L, C) = I));

   function Element (L : List; C : Cursor) return Element_Type with
     Pre  => Has_Element (L, C),
     Post => Element'Result = Get (Model (L), Position (L, C));

   function Has_Element (L : List; C : Cursor) return Boolean with
     Post => Has_Element'Result = (Position (L, C) in 1 .. Length (Model (L)));

   procedure Append (L : in out List; E : Element_Type) with
     Post => length (Model (L)) = Length (Model (L))'Old + 1
     and Get (Model (L), Length (Model (L))) = E
     and (for all I in 1 .. Length (Model (L))'Old =>
            Get (Model (L), I) = Get (Model (L'Old), I));

   function Init (N : Natural; E : Element_Type) return List with
     Post => length (Model (Init'Result)) = N
       and (for all F of Init'Result => F = E);

Elements of lists can only be accessed through cursors. To specify easily the
effects of position-based operations such as ``Append``, we introduce a ghost
type ``Sequence``, that is used to represent logically the content of the linked
list in specifications.
The sequence associated to a list can be constructed using the ``Model``
function. Following the usual translation scheme for quantified expressions, the
last line of the postcondition of ``Init`` is translated for proof as (not Ada syntax):

::

  (for all C : Cursor =>
      (if Has_Element (Init'Result, C) then Element (Init'Result, C) = E));

Using the definition of ``Element`` and ``Has_Element``, it can then be refined
further into:

::

  (for all C : Cursor =>
      (if Position (Init'Result, C) in 1 .. Length (Model (Init'Result))
       then Get (Model (Init'Result), Position (Init'Result, C)) = E));

To be able to link this property with other properties specified directly on
models, like the postcondition of ``Append``, it needs to be lifted to iterate
over positions instead of cursors. This can be done using the postcondition of
``Model`` that states that there is a valid cursor in ``L`` for each position of
its model. This lifting requires a lot of quantifier reasoning from the prover,
thus making proofs more difficult.

The |GNATprove| ``Iterable_For_Proof`` annotation can be used to provide
|GNATprove| with a `Model` function, that will be to translate quantification on
complex containers toward quantification on their model. For example, on our
lists, we could write:

.. code-block:: ada

   function Model (L : List) return Sequence with
     Annotate => (GNATprove, Iterable_For_Proof, "Model");

With this annotation, the postcondition of ``Init`` is translated directly as a
quantification on the elements of the result's model (not Ada syntax):

::

  (for all I : Positive =>
     (if I in 1 .. Length (Model (Init'Result)) then
        Get (Model (Init'Result), I) = E));

Like with the previous annotation, care should be taken to define the model
function such that it always return a model containing exactly the same elements
as ``L``.

.. note::

   It is not possible to specify more than one ``Iterable_For_Proof`` annotation
   per container type with an ``Iterable`` aspect.

.. index:: Annotate; Inline_For_Proof

Annotation for Inlining Functions for Proof
-------------------------------------------

Contracts for functions are generally translated by |GNATprove| as axioms on
otherwise undefined functions. As an example, consider the following function:

::

    function Increment (X : Integer) return Integer with
      Post => Increment'Result >= X;

It will be translated by GNATprove as follows (not Ada syntax):

::

    function Increment (X : Integer) return Integer;

    axiom : (for all X : Integer. Increment (X) >= X);

For internal reasons due to ordering issues, expression functions are also
defined using axioms. For example:

.. code-block:: ada

    function Is_Positive (X : Integer) return Boolean is (X > 0);

will be translated exactly as if its definition was given through a
postcondition, namely:

::

    function Is_Positive (X : Integer) return Boolean;

    axiom : (for all X : Integer. Is_Positive (X) = (X > 0));

This encoding may sometimes cause difficulties to the underlying solvers,
especially for quantifier instantiation heuristics. This can cause strange
behaviors, where an assertion is proven when some calls to expression
functions are manually inlined but not without this inlining.

If such a case occurs, it is sometimes possible to instruct the tool to inline
the definition of expression functions using pragma or aspect ``Annotate``
``Inline_For_Proof``. When such a pragma is provided for an expression
function, a direct definition will be used for the function instead of an
axiom:

.. code-block:: ada

    function Is_Positive (X : Integer) return Boolean is (X > 0) with
      Annotate => (GNATprove, Inline_For_Proof);

The same annotation will also allow to inline a regular function, if its
postcondition is simply an equality between its result and an expression:

.. code-block:: ada

    function Is_Positive (X : Integer) return Boolean with
      Post => Is_Positive'Result = (X > 0)
      Annotate => (GNATprove, Inline_For_Proof);

In this case, |GNATprove| will introduce a check when verifying the body of
``Is_Positive`` to make sure that the inline annotation is correct, namely, that
``Is_Positive (X)`` and ``X > 0`` always yield the same result. This check
may not be redundant with the verification of the postcondition of
``Is_Positive`` if the ``=`` symbol on booleans has been overridden.

Note that, since the translation through axioms is necessary for ordering
issues, this annotation can sometimes lead to a crash in GNATprove. It is the
case for example when the definition of the function uses quantification over a
container using the ``Iterable`` aspect.

.. index:: Annotate; Prophecy Variable

.. _Referring to a value at the end of a borrow:

Annotation for Referring to a Value at the End of a Local Borrow
----------------------------------------------------------------

Local borrowers are objects of an anonymous access-to-variable type. At their
declaration, the ownership of (a part of) an existing data-structure is
temporarily transferred to the new object. The borrowed data-structure
will regain ownership afterward.
During the lifetime of the borrower, the borrowed object can be accessed
indirectly through the borrower. It is forbidden to modify or even read the
borrowed object during the borrow.
As an example, let us consider a recursive type of singly-linked lists:

.. code-block:: ada

    type List;
    type List_Acc is access List;
    type List is record
       Val  : Integer;
       Next : List_Acc;
    end record;

Using this type, let us construct a list ``X`` which stores the numbers from
1 to 5:

.. code-block:: ada

    X := new List'(1, null);
    X.Next := new List'(2, null);
    X.Next.Next := new List'(3, null);
    X.Next.Next.Next := new List'(4, null);
    X.Next.Next.Next.Next := new List'(5, null);

We can borrow the structure designated by ``X`` in a local borrower ``Y``:

.. code-block:: ada

   declare
      Y : access List := X;
   begin
      V := Y.Val; --  OK, ownership has been transferred to Y temporarily
      V := X.Val; --  Illegal, X does not have ownership during the scope of Y
   end;

While in the scope of ``Y``, the ownership of the list designated by ``X`` is
transferred to ``Y``, so that it is not allowed to access it from ``X``
anymore. After the end of the declare block, ownership is restored to ``X``,
which can again be accessed or modified directly.

During the lifetime of the borrower, the borrowed object can be modified
indirectly through the borrower. Therefore, when the borrower goes out of scope
and ownership is transferred back to the borrowed object, |GNATprove| needs to
reconstruct the new value of the borrowed object from the value of the borrower
at the end of the borrow. In general, it can be done entirely automatically.
However, it can happen that the exact relation between the values of the
borrowed object and the borrower at the end of the borrow is lost by the tool.
In particular, it is the case when the borrower is created inside a
(traversal) function, as proof is modular on a per subprogram basis. It also
happens when the borrower is modified inside a loop, as analysing loops involves
cutpoints. In this case, |GNATprove| relies on the user to adequately
describe the link between the values of the borrowed object and the borrower at
the end of the borrow inside annotations - postconditions of traversal functions
or loop invariants.

To this effect, it is possible to refer to the value of a local borrower or a
borrowed expression at the end of the borrow using a ghost identity function
annotated with ``At_End_Borrow``. Calls to these functions are interpreted by
the tool as markers of references to values at the end of the borrow:

.. code-block:: ada

   function At_End_Borrow (E : access constant List_Acc) return access constant List_Acc is
     (E)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

Note that the name of the function could be something other than
``At_End_Borrow``.
|GNATprove| will check that a function associated with the ``At_End_Borrow``
annotation is a ghost expression function which takes a single parameter of an
access-to-constant type and returns it. ``At_End_Borrow`` functions can only be
called inside regular assertions or contracts, within a parameter of a call
to a lemma subprogram, or within the initialization of a (ghost) constant
of anonymous access-to-constant type.

When |GNATprove| encounters a call to such a function, it checks that the
actual parameter of the call is either a local borrower or an
expression which is borrowed in the current scope. It does not interpret it as
the current value of the expression, but rather as what is usually called a
`prophecy variable` in the literature, namely, an imprecise value
representing the value that the expression will have at the end of the borrow.
As |GNATprove| does not do any look-ahead, nothing will be known about the
actual value of a local borrower at the end of the borrow.
However, the tool will still
be aware of the relation between this final value and the final value of the
expression it borrows. As an example, consider a local borrower ``Y`` of the
list ``X`` as defined above. The ``At_End_Borrow`` function can be used
to give properties that are known to hold during the scope of ``Y``.
For example, since ``Y`` and ``X`` designate the same value, |GNATprove| can
verify that no matter what happens during the scope of ``Y``, at the end of the
borrow, the ``Val`` component of ``X`` will be the ``Val`` component of ``Y``:

.. code-block:: ada

   pragma Assert (At_End_Borrow (X).Val = At_End_Borrow (Y).Val);

However, even though at the beginning of the declare block, the first value of
``X`` is 1, it is not correct to assert that it will necessarily be so at the
end of the borrow:

.. code-block:: ada

   pragma Assert (Y.Val = 1);                 --  proved
   pragma Assert (At_End_Borrow (X).Val = 1); --  incorrect

Indeed, ``Y`` could be modified later so that ``X.Val`` is not 1 anymore:

.. code-block:: ada

   declare
      Y : access List := X;
   begin
      Y.Val := 2;
   end;
   pragma Assert (X.Val = 2);

Note that the assertion above is invalid even if ``Y.Val`` is `not` modified in
the following statements. It needs to be provable only from the information
available at the assertion point, not knowing what will actually happen later
in the scope of the borrow. The analysis performed by |GNATprove| only
considers those statements that occur before the assertion to be proved;
|GNATprove| does not consider statements that occur later in the control flow.
In other words, there is no lookahead when an assertion is to be proved.

.. note::

   Since ``At_End_Borrow`` functions are identity functions, the current values
   of the borrower and borrowed expression are used when executing assertions
   containing prophecy variables. This is sound. Indeed, |GNATprove| will show
   that the assertion holds for all possible modifications of the borrower. As
   not modifying the borrower is a valid senario, this is enough to ensure that
   the assertion necessarily evaluates to True at runtime.

Let us now consider a case where ``X`` is not borrowed completely. In the
declaration of ``Y``, we can decide to borrow only the last three elements of
the list:

.. code-block:: ada

   declare
      Y : access List := X.Next.Next;
   begin
      pragma Assert (At_End_Borrow (X.Next.Next).Val = At_End_Borrow (Y).Val);
      pragma Assert (At_End_Borrow (X.Next.Next) /= null);
      -- Proved, this follows from the relationship between X and Y

      pragma Assert (At_End_Borrow (X.Next.Next.Val) = 3);
      -- Incorrect, X could be modified through Y

      X.Val := 42;
   end;

Here, like in the previous example, we can state that, at the end of the borrow,
``X.Next.Next.Val`` is ``Y.Val``, and then ``X.Next.Next`` cannot be set to
null. We cannot assume anything about the
part of ``X`` designated by ``Y``, so we won't be able to prove that
``X.Next.Next.Val`` will remain 3. Note that we cannot get the value at the
end of the borrow of an expression which is not borrowed in the current scope.
Here, even if ``X.Next.Next`` is borrowed, ``X`` and ``X.Next`` are not. As
a result, calls to ``At_End_Borrow`` on them will be rejected by the tool.

Inside the scope of ``Y``, it is possible to modify the variable ``Y`` itself,
as opposed to modifying the structure it designates, so that it gives access to
a subcomponent of the borrowed structure. It is called a `reborrow`. During a
reborrow, the part of the structure designated by the borrower is reduced, so
the prophecy variable giving the value of the borrower at the end of the
borrow is reduced as well. The part of the borrowed expression which is no
longer accessible through the borrower cannot be modified anymore for the
rest of the borrow. It is said to be `frozen` and its final value is known. For
example, let's use ``Y`` to borrow ``X`` entirely and then modify it to only
designate ``X.Next.Next``:

.. code-block:: ada

   declare
      Y : access List := X;
   begin
      Y := Y.Next.Next; -- reborrow

      pragma Assert (At_End_Borrow (X).Next.Next /= null);
      pragma Assert (At_End_Borrow (X).Val = 1);
      pragma Assert (At_End_Borrow (X).Next.Val = 2);
      pragma Assert (At_End_Borrow (X).Next.Next.Val = 3);      --  incorrect
      pragma Assert (At_End_Borrow (X).Next.Next.Next /= null); --  incorrect
   end;

After the reborrow, the part of ``X`` still accessible from the borrower is
reduced, but since ``X`` was borrowed entirely to begin with, the ownership
policy of |SPARK| still forbids direct access to any components of ``X`` while
in the scope of ``Y``. As a result, we have more information about the
final value of ``X`` than in the previous case. We still know that ``X``
will hold at least three elements, that is ``X.Next.Next /= null``.
Additionally, the first and second components of ``X`` are no longer accessible
from ``Y``, and since they cannot be accessed directly through ``X``, we know
that they will keep their current values. This is why we can now assert that,
at the end of the borrow,  ``X.Val`` is 1 and ``X.Next.Val`` is 2.
However, we still cannot know anything
about the part of ``X`` still accessible from ``Y`` as these properties
could be modified later in the borrow:

.. code-block:: ada

      Y.Val := 42;
      Y.Next := null;

During sequences of re-borrows, it is additionally possible to
use constants of anonymous access-to-constant type in order to save
prophecy variables for intermediate values of an access variable, as
in the following example:

.. code-block:: ada

   declare
      Y : access List := X;
   begin
      Y := Y.Next; --  first reborrow
      declare
         Z : constant access constant List := At_End_Borrow (Y) with Ghost;
         --  At_End_Borrow is Ghost, so Z too.
      begin
         Y := Y.Next; -- second reborrow
         pragma Assert (At_End_Borrow (X).Next.Val = Z.Val);
         --  Z match prophecy of first reborrow of Y
         pragma Assert (Z.Next.Val = At_End_Borrow (Y).Val);
      end
   end

As ``Z`` serves to save a prophecy variable, it is subject to the same
usage restrictions as the corresponding ``At_End_Borrow (Y)`` call, in place
of the usual rules for local observers.

As said earlier, in general, |GNATprove| can handle local borrows without
any additional user written annotations. Therefore, ``At_End_Borrow`` functions
are mostly useful at places where information is lost by the tool: in
postconditions of borrowing traversal functions (which return a local
borrower of their first parameter) and in loop invariants if the
loop involves a reborrow (in this case the value of the borrower at the end
of the borrow is modified inside the loop and needs to be described in the
invariant). Let us consider the following example:

.. literalinclude:: /examples/ug__at_end_borrow/list_borrows.adb
   :language: ada
   :linenos:

The function ``Tail`` is a borrowing traversal function. It
returns a local borrower of its parameter ``L``. As |GNATprove| works modularly
on a per subprogram basis, it is necessary to specify in its postcondition how
the value of the borrowed parameter ``L`` can be reconstructed from the value
of the borrower ``Tail'Result`` at the end of the borrow. Otherwise, |GNATprove|
would not be able to recompute the value of the borrowed parameter after the
returned borrower goes out of scope in the caller.

The ``Tail`` function returns the ``Next`` component of a list if there is one,
and ``null`` otherwise. As pointer equality is not allowed in |SPARK|, we
define our own equality function ``Eq`` which compares the elements of the list
one by one. Note that the ``Get`` function indexes the list from the end (the
first element of the list is accessed by ``Get (L, Length (L))``). This is
done to avoid arithmetic in the recursive definition of ``Get`` as it slows
the proofs down.
In the postcondition of ``Tail``, we consider the two cases, and, in each case,
specify both the value returned by the function and how the
parameter ``L`` is related to the returned borrower:

* If ``L`` is ``null`` then ``Tail`` returns ``null`` and ``L`` will stay
  ``null`` for the duration of the borrow.
* Otherwise, ``Tail`` returns ``L.Next``, the first element of ``L`` will stay
  as it was at the time of call, and the rest of ``L`` stays equal to the object
  returned by ``Tail``.

Thanks to this postcondition, |GNATprove| can verify a program which borrows a
part of ``L`` using the ``Tail`` function and modifies ``L`` through this
borrower, as can be seen in the body of ``List_Borrows``.

Postconditions of borrowing traversal functions systematically need to provide
two properties: one specifying the result, and another specifying how the
parameter is related to the borrower. This is generally redundant, as by
nature the parameter/borrower relation always holds at the
point of return of the function.
For example, on the post of ``Tail``, ``Eq (L.Next, Tail'Result)`` repeats
``Eq (At_End_Borrow (L).Next, At_End_Borrow (Tail'Result))``.

The tool limits that redundancy by letting the user write only the
parameter/borrower relation. Properties of the result are automatically derived
by duplicating the postcondition, with calls to ``At_End_Borrow`` replaced by
their arguments. This covers most (if not all) properties of the result,
and additional properties of the result can be explicitly written if needed.
This means we get equivalent behavior for function ``Tail``
by removing the second conjunct of the postcondition.

``At_End_Borrow`` functions are also useful to write loop invariants in loops
involving reborrows. This is exemplified in the ``Set_All_To_Zero`` procedure
which traverses a list and sets all its elements to 0. The variable ``X``
borrows the whole input list ``L`` at the beginning of the function. Inside the
loop, ``X`` is used to modify the structure designated by ``L``. At the end of
the procedure, ownership is transferred back to ``L`` automatically. To
prove the postcondition of ``Set_All_To_Zero``, |GNATprove| needs to know
precisely how to reconstruct the value of ``L`` at this point. As ``X`` is
reborrowed in the loop, the relation between its value and the value of ``L`` at
the end of the borrow (the end of the scope of ``X``) changes at each iteration.
At the beginning of the loop, ``X`` is an alias of ``L``, so the value
designated by ``L`` is equal to the value designated by ``X`` at the end of the
borrow. At each iteration, an element is dropped from ``X``, so the value
designated by the current value of ``X`` at the end of the borrow shrinks. At
the same time, we get more information about the value designated by ``L`` at
the end of the borrow as more and more elements are `frozen` and therefore
definitely set to their current value, that is, 0.

Because proof uses cutpoints to reason about loops, it is necessary to supply
all this information in a loop invariant. This is what is done in the body of
``Set_All_To_Zero``. To help readability, a ghost variable ``C`` is introduced
to count the number of iterations in the loop. The first invariant is a regular
invariant, it maintains the value of ``C`` at each iteration. The two following
ones are used to describe how ``L`` can be reconstructed from ``X`` at the
end of the borrow: ``L`` will be made of ``C`` zeros followed by the final
value of ``X``. Note that, in the invariant, no assumption is made about the
changes that can be made to ``X`` during the rest of the borrow, there is no
look ahead. Both ``Tail`` and ``Set_All_To_Zero`` can be entirely verified
by |GNATprove|:

.. literalinclude:: /examples/ug__at_end_borrow/test.out
   :language: none
   :linenos:

Annotation for Accessing the Logical Equality for a Type
--------------------------------------------------------

In Ada, the equality is not the logical equality in general. In particular,
arrays are considered to be equal if they contain the same elements, even with
different bounds, +0.0 and -0.0 are considered equal...

It is possible to use a pragma or aspect ``Annotate`` to ask
|GNATprove| to interpret a function with an equality profile as the logical
equality for the type. If the function body is visible in
|SPARK|, a check will be emitted to ensure that it indeed checks for logical
equality as understood by the proof engine (which depends on the underlying
model used by the tool, see below).
It comes in handy for example to express that a (part of a) data-structure
is left unchanged by a procedure, as is done in the example below:

.. code-block:: ada

   subtype Length is Natural range 0 .. 100;
   type Word (L : Length := 0) is record
      Value : String (1 .. L);
   end record;
   function Real_Eq (W1, W2 : String) return Boolean with
     Ghost,
     Import,
     Annotate => (GNATprove, Logical_Equal);
   type Dictionary is array (Positive range <>) of Word;

   procedure Set (D : in out Dictionary; I : Positive; W : String) with
     Pre  => I in D'Range and W'Length <= 100,
     Post => D (I).Value = W
     and then (for all J in D'Range =>
                 (if I /= J then Real_Eq (D (J).Value, D'Old (J).Value)))
   is
   begin
      D (I) := (L => W'Length, Value => W);
   end Set;

The actual interpretation of logical equality is highly dependent on the
underlying model used for formal verification. However, the following
properties are always valid, no matter the actual type on which a logical
equality function applies:

* Logical equality functions are equivalence relations, that is, they are
  reflexive, symmetric, and transitive. This implies that such functions can
  always be used to express that something is preserved as done above.

* There is no way to tell the
  difference between between two values which are logically equal. Said
  otherwise, all |SPARK| compatible functions will return the same result on
  logically equal inputs. Note that Ada functions which do not follow |SPARK|
  assumptions may not, for example, if they compare the address of pointers
  which are not modelled by |GNATprove|. Such functions should never be used
  inside |SPARK| code as they can introduce soundness issues.

* Logical equality is handled efficiently, in a builtin way, by the underlying
  solvers. This is different from the regular Ada equality which is basically
  handled as a function call, using potentially complex defining axioms (in
  particular Ada equality over arrays involves quantifiers).

.. note::

  In Ada, copying an expression might not necessarily return a logically equal
  value. This happens for example when a value is assigned into a variable or
  returned by a function. Indeed, such copies might involve for example
  sliding (for arrays) or a partial copy (for view conversions of tagged types).

For most types, it is possible to provide a |SPARK| body for a logical equality
function. More precisely, logical equality can be implemented
using the regular Ada equality for discrete types and fixed point types.
For floating point types, both the value and the sign need to be compared
(to tell the difference between +0.0 and -0.0). Logical equality on constrained
arrays and untagged records can be achieved by comparing the components. In
addition, it is necessary to compare the bounds of unconstrained arrays. Since
the address of access-to-object types is not modeled in SPARK, logical equality
should return true if either both pointers are null or they designate logically
equal values.
This is examplified below:

.. literalinclude:: /examples/ug__logical_eq_implementation/logical_equality_implementation.ads
   :language: ada
   :linenos:

All logical equality annotations are proved on this example:

.. literalinclude:: /examples/ug__logical_eq_implementation/test.out
   :language: none
   :linenos:

For tagged records, the fact that functions of a specific tagged types might be
used on any descendent make it impossible to implement the logical equality in
|SPARK| in general. However, it can be done if the tag is specifically known by
comparing the components like for untagged records. In a similar way, logical
equality cannot be implemented for partially intialized data-structures
annotated with ``Relaxed_Initialization``.

Additionally, a user can safely annotate a comparison function on private types
whose full view is not in |SPARK| using the ``Logical_Equal`` annotation if it
behaves as expected, namely, it is an equivalence relation, and there is no way,
using the API provided in the public part of the enclosing package, to tell
the difference between two values on which this function returns True.

.. note::

   For private types whose full view is not in |SPARK|, |GNATprove| will peek
   inside the full view to try and determine whether or not to interpret the
   primitive equality on such types as the logical equality.

Annotation for the Predefined Equality of Private Types
-------------------------------------------------------

In Ada, an equality operator is predefined for almost all types (except
limited types). This *predefined equality* depends on the shape of the type.
It is also possible to override the equality operator for a given type. This
overriding is called the *primitive equality* of the type. Depending on the
context, the predefined or the primitive equality of a type might be used. In
particular, implicit equality operations on types which are not record types -
in membership tests or predefined equality of composite types typically - uses
the predefined equality, even if a primitive equality is supplied for the type.

In general, predefined equality operators are handled precisely by |GNATprove|
following the semantics of Ada. However, when the full view of a private type
is not visible in |SPARK|, it might not be possible to do so. In this case,
|GNATprove| approximates the behavior of the predefined equality by peeking
beyond ``SPARK_Mode`` boundaries into the full view of the type. If it can
determine that it is safe to do so, it will handle the predefined equality of
a private type as the logical equality (see
:ref:`Annotation for Accessing the Logical Equality for a Type`). Otherwise,
the predefined equality of the private type will be left unspecified and nothing
will be provable about it.

It is possible for a user to short-circuit this mechanism and instead specify
directly on a private type whose full view is not in |SPARK| how the predefined
equality should be handled using the ``Predefined_Equality`` annotation. If this
annotation is provided on a type, it will be trusted and |GNATprove| will not
peek into the full view. For now, the following profiles are supported:

- ``No_Equality``: |GNATprove| will make sure that the predefined equality of
  the private type is never used. It can be a good way to ensure that users of a
  library use the primitive equality instead. This is the default handling of
  |GNATprove| for visible composite types containing a component of an
  access-to-object type.

- ``Only_Null``: |GNATprove| will make sure that the predefined equality of
  the private type is only used when one of the operands is a specific constant
  annotated as the ``Null_Value``. This is the default handling of
  |GNATprove| for visible access-to-object types.

As an example consider the following package. An appropriate equality for the
``Unbounded_String`` type is provided as a primitive equality in
``Unbounded_Strings``. The ``Predefined_Equality`` annotation is used to make
sure that its predefined equality will never be called by programs using this
library. It is necessary in particular so that the ``To_Unbounded_String``
function can be used safely even though it will produce different pointers each
time it is called.

.. code-block:: ada

   package Unbounded_Strings is

      type Unbounded_String is private with
        Default_Initial_Condition => False,
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");

      function "=" (X, Y : Unbounded_String) return Boolean;

      function To_Unbounded_String (S : String) return Unbounded_String;

      function To_String (S : Unbounded_String) return String;

   private
      pragma SPARK_Mode (Off);

      type Unbounded_String is not null access constant String;

      function "=" (X, Y : Unbounded_String) return Boolean is (X.all = Y.all);

      function To_Unbounded_String (S : String) return Unbounded_String is
        (new String'(S));

      function To_String (S : Unbounded_String) return String is
        (S.all);

   end Unbounded_Strings;

It would be possible instead to provide a specific
``Null_String`` value on which the predefined equality is allowed:

.. code-block:: ada

   package Unbounded_Strings is

      type Unbounded_String is private with
        Default_Initial_Condition => Unbounded_String = Null_String,
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");

      Null_String : constant Unbounded_String with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");

      function To_Unbounded_String (S : String) return Unbounded_String;

      function To_String (S : Unbounded_String) return String with
        Pre => S /= Null_String;

   private
      pragma SPARK_Mode (Off);

      type Unbounded_String is access constant String;

      Null_String : constant Unbounded_String := null;

      function To_Unbounded_String (S : String) return Unbounded_String is
        (new String'(S));

      function To_String (S : Unbounded_String) return String is
        (S.all);

   end Unbounded_Strings;

Annotation for Enforcing Ownership Checking on a Private Type
-------------------------------------------------------------

Private types whose full view is not in |SPARK| can be annotated with a
pragma or aspect ``Annotate`` for ownership. Such a type is handled by
|GNATprove| in accordance to the :ref:`Memory Ownership Policy` of |SPARK|.
For example, the type ``T`` declared in the procedure ``Simple_Ownership``
below has an ownership annotation. As a result, |GNATprove| will reject the
second call to ``Read`` in the body of ``Simple_Ownership``, because the value
designated by ``X`` has been moved by the assignment to ``Y``.

.. literalinclude:: /examples/ug__ownership_annotations/simple_ownership.adb
   :language: ada
   :linenos:

In addition, it is possible to state that a such type needs reclamation by
supplying the ``"Needs_Reclamation"`` string literal as a third parameter to the
aspect or pragma ``Annotate`` for ownership. In
this case, |GNATprove| emits checks to ensure that the resource is not leaked.
For these checks to be handled precisely, the user should provide a way for
the tool to check that an object has been reclaimed. This can be done by
annotating a function which takes a value of this type as a parameter and
returns a boolean with a pragma or aspect ``Annotate`` for ownership whose
third parameter is either ``"Needs_Reclamation"`` or ``"Is_Reclaimed"``. This
function is used to check that the resource cannot be leaked. A function
annotated with ``"Needs_Reclamation"`` shall return True when its input holds
some resource while a function annotated with ``"Is_Reclaimed"`` shall return
True when its input has already been reclaimed. Another possibility is to
annotate a constant of the type with a pragma or aspect ``Annotate`` for
ownership whose third parameter is ``"Reclaimed_Value"``. Objects are
considered to be reclaimed if they are equal to the provided constant. Note
that constants annotated with ``"Reclaimed_Value"`` are not considered to hold
resources themselves, so they can be duplicated. Only one such function or
constant shall be provided for a given type. Three examples of use are given
below.

.. literalinclude:: /examples/ug__ownership_annotations/hidden_pointers.ads
   :language: ada
   :linenos:

The package ``Hidden_Pointers`` defines a type ``Pool_Specific_Access`` which
is really a pool specific access type. The ownership annotation on
``Pool_Specific_Access`` instructs |GNATprove| that objects of this type
should abide by the :ref:`Memory Ownership Policy` of SPARK. It also states
that the type needs reclamation when a value is finalized. Because of the
annotation on the ``Is_Null`` function, |GNATprove| will attempt to prove that
``Is_Null`` returns True when an object of type ``Pool_Specific_Access`` is
finalized unless it was moved.

The mechanism can also be used for resources which are not linked to memory
management. For example, the package ``Text_IO`` defines a limited type
``File_Descriptor`` and uses ownership annotations to force |GNATprove| to
verify that all file descriptors are closed before being finalized.

.. literalinclude:: /examples/ug__ownership_annotations/text_io.ads
   :language: ada
   :linenos:

In our last example, the ownership annotation is used to enforce the
:ref:`Memory Ownership Policy` of |SPARK| on pointers used to represent
strings compatible with C. Note that the ``New_String`` function has to be
volatile as the predefined equality can be used on ``Chars_Ptr`` (it is not
visibly a pointer), so ``New_String`` will return visibly different values
each time it is called.

.. literalinclude:: /examples/ug__ownership_annotations/c_strings.ads
   :language: ada
   :linenos:

.. note::
   The equality used to check whether an object is equal to a reclaimed value
   is the same as the equality used by membership tests and equality of
   composite types: it uses the predefined equality even if it has been
   redefined by the user, unless the type of the operands is ultimately a
   record type in which case it uses the primitive equality.

Annotation for Instantiating Lemma Procedures Automatically
-----------------------------------------------------------

As featured in :ref:`Manual Proof Using User Lemmas`, it is possible to write
lemmas in |SPARK| as ghost procedures. However, actual calls to the procedure
need to be manually inserted in the program whenever an instance of the
lemma is necessary.
It is possible to use an aspect or pragma ``Annotate`` to instruct |GNATprove|
that an axiom should be introduced for a lemma procedure so manual
instantiations are no longer necessary. This annotation is called
``Automatic_Instantiation``. As an example, the ``Equivalent`` function below
is an equivalence relation. This is expressed using three lemma procedures
which should be instantiated automatically:

.. code-block:: ada

   function Equivalent (X, Y : Integer) return Boolean with
     Global => null;

   procedure Lemma_Reflexive (X : Integer) with
     Ghost,
     Global => null,
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => Equivalent (X, X);

   procedure Lemma_Symmetric (X, Y : Integer) with
     Ghost,
     Global => null,
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre  => Equivalent (X, Y),
     Post => Equivalent (Y, X);

   procedure Lemma_Transitive (X, Y, Z : Integer) with
     Ghost,
     Global => null,
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre  => Equivalent (X, Y) and Equivalent (Y, Z),
     Post => Equivalent (X, Z);

Such lemmas should be declared directly after a function declaration, here the
``Equivalent`` function. The axiom will only be available when the associated
function is used in the proof context.

Annotation for Managing the Proof Context
-----------------------------------------

By default, when verifying a part of a program, |GNATprove| chooses which
information is available for proof based on a liberal notion of visibility:
everything is visible except if it is declared in the body of another
(possibly nested) unit. It assumes values of
global constants, postconditions of called subprograms, bodies of expression
functions... This behavior can be tuned either globally or, in some cases,
specificaly for the analysis of a given unit, using the dual annotations
``Hide_Info`` and ``Unhide_Info``.

Overriding the Default Handling of Visibility
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The private part of withed units is visible by |GNATprove| by default if it is
in |SPARK|. This is useful in particular for units which declare private types
as it makes it optional for users to introduce a proper abstraction for these
types. As an example, consider the following package:

.. literalinclude:: /examples/ug__hide_private_no_annot/geometry.ads
   :language: ada
   :linenos:

The package ``Geometry`` is not annotated with any contract. However, as its
private part is visible, it is still possible to prove programs using this
library:

.. literalinclude:: /examples/ug__hide_private_no_annot/use_geometry.adb
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__hide_private_no_annot/test.out
   :language: none
   :linenos:

This behavior is useful in general. However, when designing complex libraries,
it might be interesting to enforce abstraction in order to reduce the
proof context in user code. It can be done by using a ``Hide_Info`` annotation
at the top of the private part of a package:

.. literalinclude:: /examples/ug__hide_private_annot/geometry.ads
   :language: ada
   :linenos:

Such an annotation is only allowed on library-level packages that are visible
from outside the library unit. This excludes in particular nested packages in
a package body or in a private child package. They cause the private
parts of annotated packages to no longer be visible when verifying
user code. However, they remain visible when analysing enclosing units and
child packages. Note that using this annotation generally requires users to
write additional contracts for user code to remain provable. In particular,
this might include getter or model functions as well as a user-defined
primitive equality with a contract. As an example, with this annotation and
no other changes, ``Use_Geometry`` becomes impossible to prove:

.. literalinclude:: /examples/ug__hide_private_annot/test.out
   :language: none
   :linenos:

Retaining provability can be done for example by introducing ghost functions
returning the width and the heigth of a rectangle and using them in the
contracts of other functions. The obvious duplication here is the reason why
abstraction is not enforced on private parts by default:

.. literalinclude:: /examples/ug__hide_private_abstraction/geometry.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__hide_private_abstraction/test.out
   :language: none
   :linenos:

.. note::

   Private types declared in packages with hidden private parts should be
   annotated with ``Ownership`` and ``Predefined_Equality`` annotations if
   their full view is subject to ownership or if its predefined equality is
   restricted (in particular if they have access parts). Otherwise, |GNATprove|
   rejects the code with an error. See
   :ref:`Annotation for Enforcing Ownership Checking on a Private Type`
   and :ref:`Annotation for the Predefined Equality of Private Types` for more
   information.

By default, refined postconditions and bodies of expression functions declared
in the body of a package are not visible from outside of this package. This
enforces abstraction and prevents the proof context from growing too much, in
particular with generic instantiations. However, it can be the case that the
information hidden in the body of a nested package is in fact necessary to
prove its enclosing unit. In particular, it happens when all entities introduced
for the specification of a library are grouped together in a ghost nested
package:

.. code-block:: ada

   package My_Lib is

      type T is private;

      package Formal_Model with Ghost is

         type Model_T is ...;

	 function Model (X : T) return Model_T;

      end Formal_Model;

      ...

   end My_Lib;

It is possible to disclose the content of the body of a nested package using
an ``Unhide_Info`` annotation. In this case, the body of expression functions
and potential refined postconditions specified in this body are visible as if
they were declared directly in the enclosing unit.


.. code-block:: ada

   package body My_Lib is

      package body Formal_Model with
         Annotate => (GNATprove, Unhide_Info, "Package_Body")
      is

	 function Model (X : T) return Model_T is (...);

      end Formal_Model;

      ...

   end My_Lib;


Pruning the Proof Context on a Case by Case Basis
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

While, in general, having information about all used entities is desirable, it
might result in untractable
proof contexts on large programs. It is possible to use an annotation to
manually add or remove information from the proof context.
For the time being, only bodies of expression functions can be handled in this
way.

Information hiding is decided at the level of an entity for which checks are
generated, namely, a subprogram or entry, or the elaboration of a package. It
cannot be refined in a smaller scope. To state that the body of an expression
function should be hidden when verifying an entity ``E``, a pragma with the
``Hide_Info`` annotation should be used either at the begining of the body of
``E`` or just after its specification or body. In the following example, the
body of the expression function ``F`` is hidden when verifying its callers,
making it impossible to prove their postconditions:

.. code-block:: ada

   function F (X, Y : Boolean) return Boolean is (X and Y);

   function Call_F (X, Y : Boolean) return Boolean is
     (F (X, Y))
   with Post => Call_F'Result = (X and Y); --  Unprovable, F is hidden
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", F);

   function Call_F_2 (X, Y : Boolean) return Boolean with
     Post => Call_F_2'Result = (X and Y); --  Unprovable, F is hidden

   function Call_F_2 (X, Y : Boolean) return Boolean is
   begin
      return F (X, Y);
   end Call_F_2;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", F);

   function Call_F_3 (X, Y : Boolean) return Boolean with
     Post => Call_F_3'Result = (X and Y); --  Unprovable, F is hidden

   function Call_F_3 (X, Y : Boolean) return Boolean is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", F);
   begin
      return F (X, Y);
   end Call_F_3;

It is also possible to hide information by default and then use an annotation to
disclose it when needed. A ``Hide_Info`` annotation located on the entity which
is hidden is considered to provide a default. For example, the body of the
expression function ``G`` is hidden by default. The postcondition of its caller
``Call_G`` cannot be proved.

.. code-block:: ada

   function G (X, Y : Boolean) return Boolean is (X and Y) with
     Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");
   --  G is hidden by default

   function Call_G (X, Y : Boolean) return Boolean is
     (G (X, Y))
   with Post => Call_G'Result = (X and Y); --  Unprovable, G is hidden

When information is hidden by default, it is possible to disclose it while
verifying an entity using the ``Unhide_Info`` annotation. This allows proving
the ``Call_G_2`` function below:

.. code-block:: ada

   function Call_G_2 (X, Y : Boolean) return Boolean is
     (G (X, Y))
   with Post => Call_G_2'Result = (X and Y); --  Provable, G is no longer hidden
   pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", G);

Remark that, when information is hidden by default, it is even hidden during
the verification of the entity whose information we are hiding. For example,
when verifying a recursive expression function whose body is hidden by default,
the body of recursive calls is not available. If necessary, it can be disclosed
using an ``Unhide_Info`` annotation:

.. code-block:: ada

   --  Rec_F is hidden for its recursive calls

   function Rec_F (X, Y : Boolean) return Boolean is
     (if not X then False elsif X = Y then True else Rec_F (Y, X))
       with
         Subprogram_Variant => (Decreases => X),
         Post => (if X then Rec_F'Result = Y), --  Unprovable, Rec_F is hidden
         Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   --  The second annotation overrides the default for recursive calls

   function Rec_F_2 (X, Y : Boolean) return Boolean is
     (if not X then False elsif X = Y then True else Rec_F_2 (Y, X))
       with
         Subprogram_Variant => (Decreases => X),
         Post => (if X then Rec_F_2'Result = Y), --  Provable, Rec_F_2 is visible
         Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");
   pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Rec_F_2);

Annotation for Handling Specially Higher Order Functions
--------------------------------------------------------

Functions for higher order programming can be expressed using parameters of an
anonymous access-to-function type. As an example, here is a function ``Map``
returning a new array whose elements are the result of the application a
function ``F`` to the elements of its input array parameter:

.. code-block:: ada

   function Map
     (A : Nat_Array;
      F : not null access function (N : Natural) return Natural)
      return Nat_Array
   with
     Post => Map'Result'First = A'First and Map'Result'Last = A'Last
       and (for all I in A'Range => Map'Result (I) = F (A (I)));

In a functional programming style, these functions are often called with an
access to a local function as a parameter. Unfortunately, as |GNATprove|
generally handles access-to-subprograms using refinement semantics, it is not
possible to use a function accessing global data as an actual for an anonymous
access-to-function parameter (see :ref:`Subprogram Pointers`). To workaround
this limitation, it is possible to annotate the function ``Map`` with
a pragma or aspect ``Annotate => (GNATprove, Higher_Order_Specialization)``.
When such a function is called on a reference to the ``Access`` attribute
of a function, it will benefit from a partial exemption from the checks
usually performed on the creation of such an access. Namely, the function will
be allowed to access data, and it might even have a precondition if it can
be proved to always hold at the point of call. We say that such a call is
`specialized` for a particular value of its access-to-function parameter.
As an example, consider the function ``Divide_All`` defined below. As the
function ``Map`` is annotated with ``Higher_Order_Specialization``, it can be
called on the function ``Divide``, even though it accesses some global data
(the parameter ``N``) and has a precondition.

.. code-block:: ada

   function Map
     (A : Nat_Array;
      F : not null access function (N : Natural) return Natural)
      return Nat_Array
   with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => Map'Result'First = A'First and Map'Result'Last = A'Last
       and (for all I in A'Range => Map'Result (I) = F (A (I)));

   function Divide_All (A : Nat_Array; N : Natural) return Nat_Array with
     Pre  => N /= 0,
     Post => (for all I in A'Range => Divide_All'Result (I) = A (I) / N);

   function Divide_All (A : Nat_Array; N : Natural) return Nat_Array is
      function Divide (E : Natural) return Natural is
        (E / N)
      with Pre => N /= 0;
   begin
      return Map (A, Divide'Access);
   end Divide_All;

.. note::

   It might not be possible to annotate a function with
   ``Higher_Order_Specialization`` if the access value of its parameter
   is used in the contract of the function, as opposed to only its dereference.
   This happens in particular if the parameter is used in a call to a function
   which does not have the ``Higher_Order_Specialization`` annotation.

Because the analysis done by |GNATprove| stays modular, the
precondition of the referenced function has to be provable on all possible
parameters (but the specialized access-to-function parameters)
and not only on the ones on which it is actually called. For
example, even if we know that the precondition of ``Add`` holds for all the
elements of the input array ``A``, there will still be a failed check on the
call to ``Map`` in ``Add_All`` defined below. Indeed, |GNATprove| does not
peek into the body of ``Map`` and therefore has no way to know that its
parameter ``F`` is only called on elements of ``A``.

.. code-block:: ada

   function Add_All (A : Nat_Array; N : Natural) return Nat_Array with
     Pre  => (for all E of A => E <= Natural'Last - N),
     Post => (for all I in A'Range => Add_All'Result (I) = A (I) + N);

   function Add_All (A : Nat_Array; N : Natural) return Nat_Array is
      function Add (E : Natural) return Natural is
        (E + N)
      with Pre => E <= Natural'Last - N;
   begin
      return Map (A, Add'Access);
   end Add_All;

To avoid this kind of issue, it is possible to write a function with no
preconditions and a fallback value as done below. Remark that this does not
prevent the tool from proving the postcondition of ``Add_All``.

.. code-block:: ada

   function Add_All (A : Nat_Array; N : Natural) return Nat_Array is
      function Add (E : Natural) return Natural is
        (if E <= Natural'Last - N then E + N else 0);
   begin
      return Map (A, Add'Access);
   end Add_All;

.. note::

   Only the regular contract of functions is available on specialized calls.
   Bodies of expression functions and refined postconditions will be ignored.

The ``Higher_Order_Specialization`` annotation can also be supplied on a lemma
procedure (see :ref:`Manual Proof Using User Lemmas`). If this procedure
has an ``Automatic_Instantiation`` annotation
(see :ref:`Annotation for Instantiating Lemma Procedures Automatically`) and its associated
function also has an ``Higher_Order_Specialization`` annotation, the lemma
will generally be instantiated automatically on specialized calls to the
function. As an example, the function ``Count`` defined below returns the number
of elements with a property in an array. The function ``Count`` is specified in
a recursive way in its postcondition. The two lemmas ``Lemma_Count_All`` and
``Lemma_Count_None`` give the value of ``Count`` when all the elements of ``A``
or no elements of ``A`` fulfill the property. They will be automatically
instantiated on all specializations of ``Count``.

.. code-block:: ada

   function Count
     (A : Nat_Array;
      F : not null access function (N : Natural) return Boolean)
      return Natural
   with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Subprogram_Variant => (Decreases => A'Length),
     Post =>
       (if A'Length = 0 then Count'Result = 0
        else Count'Result =
            (if F (A (A'Last)) then 1 else 0) +
              Count (A (A'First .. A'Last - 1), F))
       and Count'Result <= A'Length;

   procedure Lemma_Count_All
     (A : Nat_Array;
      F : not null access function (N : Natural) return Boolean)
   with
     Ghost,
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre  => (for all E of A => F (E)),
     Post => Count (A, F) = A'Length;

   procedure Lemma_Count_None
     (A : Nat_Array;
      F : not null access function (N : Natural) return Boolean)
   with
     Ghost,
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre  => (for all E of A => not F (E)),
     Post => Count (A, F) = 0;

.. note::

   It can happen that some lemmas cannot be specialized with their
   associated function. It is the case in particular if the lemma contains
   several calls to the function with different access-to-function parameters.
   In this case, a warning will be emitted on the lemma declaration.

.. index:: Annotate; Handler

Annotation for Handlers
-----------------------

Some programs define `handlers`, subprograms which might be called
asynchronously to perform specific treatments, for example when an interrupt
occurs. These handlers are often registered using access-to-subprogram
types. In general, access-to-subprograms are not allowed to access or modify
global data in |SPARK|. However, this is too constraining for handlers which
tend to work by side-effects. To alleviate this limitation, it is
possible to annotate an access-to-subprogram type with a pragma or aspect
``Annotate => (GNATprove, Handler)``. This instructs |GNATprove| that these
access-to-subprograms will be called asynchronously. It is possible to
create a value of such a type using a reference to the ``Access`` attribute
on a subprogram accessing or modifying global data, but only when this global
data is synchronized (see SPARK RM 9.1). However, |GNATprove| will make sure
that the subprograms designated by objects of these types are never called from
|SPARK| code, as it could result in a missing data dependency.

For example, consider the following procedure which resets to zero a global
variable ``Counter``:

.. code-block:: ada

   Counter : Natural := 0 with Atomic;

   procedure Reset is
   begin
      Counter := 0;
   end Reset;

It is not possible to store an access to ``Reset`` in a regular
access-to-procedure type, as it has a global effect. However, it can be stored
in a type annotated with an aspect ``Annotate => (GNATprove, Handler)`` like
below:

.. code-block:: ada

   type No_Param_Proc is access procedure with
     Annotate => (GNATprove, Handler);

   P : No_Param_Proc := Reset'Access;

However, it is not possible to call ``P`` from |SPARK| code as the effect to
the ``Counter`` variable would be missed.

.. note::

   As handlers are called asynchronously, |GNATprove| does not allow providing
   pre and postconditions for the access-to-subprogram type. As a result, a
   check will be emitted to ensure that the precondition of each specific
   subprogram designated by these handlers is provable in the empty context.

Annotation for Container Aggregates
-----------------------------------

The ``Container_Aggregates`` annotation allows specifying aggregates on types
annotated with the :ref:`Aspect Aggregate` either
directly, using predefined aggregate patterns, or through a model. The second
option is the easiest. It is enough to provide a model function returning a type
which supports compatible aggregates. When an aggregate is encountered,
|GNATprove| deduces the value of its model using the ``Container_Aggregates``
annotation on the model type. In particular, functional containers from the
:ref:`SPARK Libraries` are annotated with the ``Aggregate`` aspect. Other
container libraries can take advantage of this support to specify aggregates on
their own library by providing a model function returning a functional
container. As an example, sequences can be used as a model to provide aggregates
for a linked list of integers:

.. literalinclude:: /examples/ug__aggregate_aspect_model/through_model.ads
   :language: ada
   :linenos:

The ``Container_Aggregates`` annotation on type ``List`` indicates that its
aggregates are specified using a model function. The annotation on the ``Model``
function identifies it as the function that should be used to model aggregates
of type ``List``. It is then possible to use aggregates of type ``List`` in
|SPARK| as in the ``Main`` procedure below. |GNATprove| will use the handling of
aggregates on infinite sequences to determine the value of the model of the
aggregate and use it to prove the program.

.. literalinclude:: /examples/ug__aggregate_aspect_model/main.adb
   :language: ada
   :linenos:

It is also possible to specify directly how aggregates should be handled,
without going through a model. To do this, |GNATprove| provides three different
predefined patterns: one for vectors and sequences, one for sets,
and one for maps. The chosen pattern is specified inside the
``Container_Aggregates`` annotation on the type. Depending on this pattern,
different functions can be provided to describe it. As an example, aggregates
on our linked list of integers can also be described directly by supplying the
three functions required for predefined sequence aggregates - ``First``,
``Last``, and ``Get``:

.. literalinclude:: /examples/ug__aggregate_aspect_predefined/predefined.ads
   :language: ada
   :linenos:

For all types annotated with ``Container_Aggregates``, |GNATprove| performs
`consistency checks` to make sure that the description induced by the annotation
is compatible with the subprograms supplied by its ``Aggregate`` aspect. For
example, on the ``List`` type defined above, |GNATprove| generates checks to
ensure that ``Length`` returns ``First - 1`` on ``Empty_List``. It also checks
that calling ``Add`` increases the result of ``Length`` by one and that its
parameter ``E`` is associated to this last position. These checks succeed on
our example thanks to the postcondition of ``Add`` as made explicit by the
``info`` messages on line 8:

.. literalinclude:: /examples/ug__aggregate_aspect_predefined/test.out
   :language: none
   :lines: 5-13

The ``Container_Aggregates`` annotation might also induce
`restrictions on aggregate usage`. For example, if we had chosen a signed
integer type for the return type of ``Length`` in ``Predefined``,
|GNATprove| would have introduced checks on all aggregates of type ``List`` to
make sure that the number of elements doesn't exceed the number of indexes.

When a model is used to specify aggregates, both the restrictions on
aggregate usage and the consistency checks of the model are inherited. For
example, |GNATprove| attempts to prove the consistency of ``Empty_List``
and ``Add`` from ``Through_Model`` with the functions supplied for the model.
These checks are proved thanks to the precise postcondition on ``Add``.
In the same way, if we had chosen to use a functional vector indexed by a signed
integer type instead of an infinite sequence as a model in ``Through_Model``,
we would have been limited by the size of the integer type for our aggregates.

All types with a ``Container_Aggregates`` annotation can be supplied an
additional ``Capacity`` function. In general, this function does not have any
parameters. It provides a constant bound on the number of elements allowed in
the container. If a ``Capacity`` function is supplied on a type using models for
its aggregates, it overrides the ``Capacity`` function of the model if any.
If present, the ``Capacity`` function is used both as an additional restriction
on aggregate usage and as an additional assumption for the consistency checks:
|GNATprove| assumes that the container holds strictly less than ``Capacity``
elements before a call to ``Add`` and it makes sure that the number of elements
in actual aggregates never exceeds the capacity.

To accomodate containers which can have a different capacity depending on the
object, Ada allows providing an ``Empty`` function which takes an integer value
for the capacity as a parameter in the ``Aggregate`` aspect. If a ``Capacity``
function is specified for such a type, it shall take the container as a
parameter since the capacity is specific to each container. In this case, it is
the upper bound of the parameter type of the ``Empty`` function which is used
as a restriction on aggregate usage. Examples of containers with
a capacity function (both with and without parameters) can be found in formal
container packages in the :ref:`SPARK Libraries`.

There are three kinds of predefined aggregates patterns:
``Predefined_Sequences`` like in the ``Predefined`` package,
``Predefined_Sets``, and ``Predefined_Maps``. The selected pattern should be
provided as a string to the ``Container_Aggregates`` annotation specified on the
container type. Additional ``Container_Aggregates`` annotations are necessary on
each specific function supported by the pattern. They also require a string
encoding its intended use. This usage is examplified in
the ``Predefined`` package.

The ``Predefined_Sequences`` pattern can be applied to containers with
positional aggregates. It supports three kinds of function annotations:

* The function ``First`` returns the index or position that should be used
  for the first element in a container.

* The function ``Last`` returns the index or position of the last element
  in a specific container.

* The function ``Get`` returns the element associated to a valid index or
  position in the container.

All three functions are mandatory. The return types of ``First`` and ``Last``
should be subtypes of the same signed integer type, or possibly of
``Big_Integer``.

The consistency checks ensure that:

* ``Empty`` returns a container ``C`` such that ``Last (C) = First - 1``,

* ``Add`` can be called on a container ``C`` such that
  ``Last (C) < Index_Type'Last``, and

* after a call to ``Add``, the result of ``Last (C)`` has been incremented by
  one, the result of calling ``Get`` on all previous indexes is unchanged, and
  calling ``Get`` on the last index returns the added element.

The contracts of ``Empty`` and ``Append`` below ensure conformance to
these consistency checks:

.. code-block:: ada

   type T is private with
     Aggregate => (Empty       => Empty,
                   Add_Unnamed => Append),
     Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

   function Empty return T with
     Post => Last (Empty'Result) = First - 1;
   procedure Append (X : in out T; E : Element_Type) with
     Always_Terminates,
     Pre  => Last (X) < Index_Type'Last,
     Post => Last (X) = Last (X)'Old + 1 and Get (X, Last (X)) = E
     and (for all I in First .. Last (X) - 1 => Get (X, I) = Get (X'Old, I));

   function Last (X : T) return Ext_Index with
     Annotate => (GNATprove, Container_Aggregates, "Last");

   function First return Index_Type with
     Annotate => (GNATprove, Container_Aggregates, "First");

   function Get (X : T; I : Index_Type) return Element_Type with
     Annotate => (GNATprove, Container_Aggregates, "Get"),
     Pre => I <= Last (X);

If ``Last`` returns a signed integer type, there is a restriction on predefined
sequence aggregates usage: |GNATprove| will make sure that the number of
elements in an aggregate never exceeds the maximum value of the return type of
``Last``.

When an aggregate ``C`` is encountered, |GNATprove| automatically infers that:

* ``Last (C) - First + 1`` is the number of elements in the aggregate and

* ``Get (First + N - 1)`` returns a copy of the N'th element.

The ``Predefined_Sets`` pattern can be applied to containers with
positional aggregates. It supports three kinds of function annotations:

* The ``Contains`` function returns True if and only if its element
  parameter is in the container.

* ``Equivalent_Elements`` is an equivalence relation such that ``Contains``
  always returns the same value on two equivalent elements.

* The ``Length`` function returns the number of elements in the set.

``Contains`` and ``Equivalent_Elements`` are mandatory, ``Length`` is optional.
If it is supplied, the ``Length`` function should return a signed
integer type or a subtype of ``Big_Integer``.

The consistency checks ensure that:

*  ``Contains`` returns False for all elements on the result of ``Empty`` and
   ``Length``, if specified, returns 0,

* ``Add`` can be called on a container ``C`` and an element ``E`` such that
  ``Contains (C, E)`` returns False,

* after a call to ``Add`` on a container ``C`` and an element ``E``,
  ``Contains`` returns True on ``E`` and on all elements which were in ``C``
  before the call, plus potential additional elements equivalent to ``E``,

* after a call to ``Add``, the result of the ``Length`` function if any is
  incremented by one.

The contracts of ``Empty`` and ``Insert`` below ensure conformance to
these consistency checks:

.. code-block:: ada

   type T is private with
     Aggregate => (Empty       => Empty,
                   Add_Unnamed => Insert),
     Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

   function Empty return T with
     Post => Length (Empty'Result) = 0
     and then (for all E in Element_Type => not Contains (Empty'Result, E));
   procedure Insert (X : in out T; E : Element_Type) with
     Always_Terminates,
     Pre  => not Contains (X, E),
     Post => Length (X) = Length (X'Old) + 1 and Contains (X, E)
     and (for all F in Element_Type =>
            (if Contains (X'Old, F) then Contains (X, F)))
     and (for all F in Element_Type =>
            (if Contains (X, F) then Contains (X'Old, F) or Eq_Elem (F, E)));

   function Eq_Elem (X, Y : Element_Type) return Boolean with
     Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   function Contains (X : T; E : Element_Type) return Boolean with
     Annotate => (GNATprove, Container_Aggregates, "Contains");

   function Length (X : T) return Natural with
     Annotate => (GNATprove, Container_Aggregates, "Length");

Aggregates of types annotated with ``Predefined_Sets`` cannot contain
`duplicates`, that is, two elements on which ``Equivalent_Elements`` returns
True. This restriction on aggregate usage is enforced by |GNATprove|. It
allows the tool to properly assess the cardinality of the resulting set. If
a ``Length`` function is supplied and returns a signed integer type, and no
``Capacity`` function applies to the type, |GNATprove| also makes sure that the
number of elements in the aggregate does not exceed the upper bound of the
return type of ``Length``. This last check is replaced by a check on the
capacity if there is one.

When an aggregate ``C`` is encountered, |GNATprove| automatically infers that:

* ``Contains (C, E)`` returns True for every element ``E`` of the aggregate,

* ``Contains (C, E)`` returns False for every element ``E`` which is not
  equivalent to any element in the aggregate, and

* ``Length (C)``, if supplied, is the number of elements in the aggregate.

The ``Predefined_Maps`` pattern can be applied to containers with
named aggregates. It supports five kinds of function annotations:

* The ``Default_Item`` function returns the element associated by default to
  keys of total maps.

* The ``Has_Key`` function returns True if and only if its key parameter has an
  association in a partial map.

* The ``Get`` function returns the element associated to a key in the container.

* ``Equivalent_Keys`` is an equivalence relation such that ``Has_Key`` and
  ``Get`` return the same value on two equivalent keys.

* The ``Length`` function returns the number of associations in a partial map.

``Get`` and ``Equivalent_Keys`` are mandatory, exactly one of ``Default_Item``
and ``Has_Key`` should be supplied (depending on whether the map is total - it
associates a value to all keys - or partial) , and ``Length`` is optional and
can only be supplied for partial maps. If it is supplied, the ``Length``
function should return a signed integer type or a subtype of ``Big_Integer``.

The consistency checks ensure that:

* if ``Default_Item`` is supplied, ``Get`` returns ``Default_Item`` for all keys
  on the result of ``Empty``,

* if ``Has_Key`` is supplied, it returns False for all keys on the result of
  ``Empty``, and ``Length``, if specified, returns 0,

* ``Add`` can be called on a container ``C`` and a key ``K`` such that
  ``Has_Key (C, K)`` returns False (for patial maps) or
  ``Get (C, K) = Default_Item`` (for total maps),

* after a call to ``Add`` on a container ``C``, a key ``K``, and an element
  ``E``, ``Has_Key``, if any, returns True on ``K`` and on all keys which were
  in ``C`` before the call, plus potential additional keys equivalent to ``K``,

* after a call to ``Add`` on a container ``C``, a key ``K``, and an element
  ``E``, ``Get`` returns a copy of ``E`` on ``K`` and its association in ``C``
  before the call on keys which are not equivalent to ``K``, and

* after a call to ``Add``, the result of the ``Length`` function if any is
  incremented by one.

The contracts of ``Empty`` and ``Insert`` below ensure conformance to
these consistency checks for total maps:

.. code-block:: ada

   type T is private with
     Aggregate => (Empty     => Empty,
                   Add_Named => Insert),
     Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

   function Empty return T with
     Post => (for all K in Key_Type => Get (Empty'Result, K) = Default_Value);
   procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
     Always_Terminates,
     Pre  => Get (X, K) = Default_Value,
     Post => Get (X, K) = E
     and (for all F in Key_Type =>
            (if not Eq_Key (F, K) then Get (X, F) = Get (X'Old, F)));

   function Eq_Key (X, Y : Key_Type) return Boolean with
     Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   function Default_Value return Element_Type with
     Annotate => (GNATprove, Container_Aggregates, "Default_Item");

   function Get (X : T; K : Key_Type) return Element_Type with
     Annotate => (GNATprove, Container_Aggregates, "Get";

And here is a version for partial maps:

.. code-block:: ada

   type T is private with
     Aggregate => (Empty     => Empty,
                   Add_Named => Insert),
     Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

   function Empty return T with
     Post => Length (Empty'Result) = 0
     and (for all K in Key_Type => not Has_Key (Empty'Result, K));
   procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
     Always_Terminates,
     Pre  => not Has_Key (X, K),
     Post => Length (X) - 1 = Length (X)'Old
     and Has_Key (X, K)
     and (for all F in Key_Type =>
            (if Has_Key (X'Old, F) then Has_Key (X, F)))
     and (for all L in Key_Type =>
            (if Has_Key (X, L) then Has_Key (X'Old, L) or Eq_Key (L, K)))
     and Get (X, K) = E
     and (for all F in Key_Type =>
            (if Has_Key (X'Old, F) then Get (X, F) = Get (X'Old, F)));

   function Eq_Key (X, Y : Key_Type) return Boolean with
     Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   function Has_Key (X : T; K : Key_Type) return Boolean with
     Annotate => (GNATprove, Container_Aggregates, "Has_Key");

   function Get (X : T; K : Key_Type) return Element_Type with
     Pre => Has_Key (X, K),
     Annotate => (GNATprove, Container_Aggregates, "Get");

   function Length (X : T) return Natural with
     Annotate => (GNATprove, Container_Aggregates, "Length");

Aggregates of types annotated with ``Predefined_Maps`` cannot contain
`duplicates`, that is, two keys on which ``Equivalent_Keys`` returns
True. This restriction on aggregate usage is enforced by |GNATprove|. It
allows the tool to determine the associated element uniquely and to assess the
cardinality of the resulting map. If a ``Length`` function is supplied and
returns a signed integer type, and no ``Capacity`` function applies to the type,
|GNATprove| also makes sure that the number of elements in the aggregate does
not exceed the upper bound of the return type of ``Length``. This last check is
replaced by a check on the capacity if there is one.

When an aggregate ``C`` is encountered, |GNATprove| automatically infers that:

* if ``Has_Key`` is supplied, ``Has_Key (C, K)`` returns True for every
  association ``K => _`` in the aggregate,

* ``Get (C, K)`` returns a copy of ``E`` for every association ``K => E`` in
  the aggregate,

* for every key ``K`` which is not equivalent to any key in the aggregate
  either ``Has_Key (C, K)`` returns False (for patial maps) or ``Get (C, K)``
  returns ``Default_Item`` (for total maps), and

* ``Length (C)``, if supplied, is the number of elements in the aggregate.

Annotation for Mutable IN Parameters
------------------------------------

In |SPARK|, parameters of mode ``in`` - and every object they designate,
see :ref:`Memory Ownership Policy` - are considered to be preserved by
subprogram calls unless the parameters are of an access-to-variable type. Ada,
however, does not enforce the same restriction. In particular, if a parameter of
mode ``in`` is of a private type which is ultimately an access-to-variable type,
then the subprogram might modify the value it designates. The
``Mutable_In_Parameters`` annotation is designed to make it possible to interact
with existing Ada libraries from |SPARK| code, even if the libraries are not
abiding by the language restrictions. It allows annotating an entry, procedure,
or function with side effects so that all its parameters of mode ``in`` of
a given type are considered to be potentially modified by the subprogram. This
is only supported for parameters of a private type whose ultimate full view is
either not visible from |SPARK| or an access-to-variable type.

As an example, consider an Ada library for strings with the following signature:

.. code-block:: ada

   package My_Unbounded_Strings is

     type My_String is private;

     Null_String : constant My_String;

     function Get (S : My_String) return String with
       Pre => S /= Null_String;

     procedure Update
       (S     : My_String;
        Index : Positive;
        Char  : Character)
     with Pre =>
       S /= Null_String and then Index in Get (S)'Range;

   private

     type My_String is access String;

     Null_String : constant My_String := null;

   end My_Unbounded_Strings;


To be able to designate strings of any size, the type ``My_String`` is in fact
a pointer to an Ada string that can be retrieved through the ``Get`` function.
The ``Update`` procedure writes a character ``Char`` at position ``Index``
in the value designated by ``S``. Since the value of the pointer ``S`` is not
modified by ``Update``, Ada allows it to be a parameter of mode ``in``. However,
this procedure is not compatible with |SPARK|, as it modifies the value
designated by ``Item`` which is considered to be part of ``Item`` as per the
:ref:`Memory Ownership Policy`. To make it possible to use this procedure from
|SPARK| code, a ``pragma Annotate`` is supplied directly after ``Update``:

.. code-block:: ada

   pragma Annotate (GNATprove, Mutable_In_Parameters, My_String);

Thanks to this annotation, |GNATprove| considers that a call to ``Update`` can
modify its parameter ``Item``, even if it has mode ``in``.

.. note::

   This pragma ``Annotate`` does not designate a parameter by name but the
   parameter type (because the scope of the parameter entity is limited to the
   declaration of the enclosing subprogram). It can happen that the same type
   is used for more than one parameter of mode ``in`` in the subprogram. If it
   is the case, all such parameters will be considered to be potentially mutated
   by the call. If some are in fact preserved, it will need to be stated as a
   postcondition of the subprogram.
