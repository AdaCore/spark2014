Aspects or Pragmas Specific to GNATprove
========================================

This appendix lists all the aspects or pragmas specific to |GNATprove|,
in particular all the uses of aspect or pragma ``Annotate`` for
|GNATprove|.  Aspect or pragma ``Annotate`` can also be used to control other
AdaCore tools. The uses of such annotations are explained in the User's guide
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
    pragma Annotate (GNATprove, <annotation name>, Func);

In the following, we use the aspect form whenever possible.

.. index:: Annotate; False_Positive
           Annotate; Intentional

Using Annotations to Justify Check Messages
-------------------------------------------

You can use annotations of the form

.. code-block:: ada

    pragma Annotate (GNATprove, False_Positive,
                     "message to be justified", "reason");

to justify an unproved check message that cannot be proved by other means. See
the section :ref:`Direct Justification with Pragma Annotate` for more details
about this use of pragma ``Annotate``.

.. index:: Annotate; No_Wrap_Around

Using Annotations to Request Skipping Parts of the Analysis for an Entity
-------------------------------------------------------------------------

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

Using Annotations to Request Overflow Checking on Modular Types
---------------------------------------------------------------

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

.. index:: Annotate; Iterable; Iterable_For_Proof

Customize Quantification over Types with the Iterable Aspect
------------------------------------------------------------

In |SPARK|, it is possible to allow quantification over any container type
using the ``Iterable`` aspect.
This aspect provides the primitives of a container type that will be used to
iterate over its content. For example, if we write:

.. code-block:: ada

   type Container is private with
     Iterable => (First       => First,
                  Next        => Next,
                  Has_Element => Has_Element);

where

.. code-block:: ada

   function First (S : Set) return Cursor;
   function Has_Element (S : Set; C : Cursor) return Boolean;
   function Next (S : Set; C : Cursor) return Cursor;

then quantification over containers can be done using the type ``Cursor``. For
example, we could state:

.. code-block:: ada

   (for all C in S => P (Element (S, C)))

to say that ``S`` only contains elements for which a property ``P`` holds. For
execution, this expression is translated as a loop using the provided ``First``,
``Has_Element``, and ``Next`` primitives. For proof, it is translated as a logic
quantification over every element of type ``Cursor``. To restrict the property
to cursors that are actually valid in the container, the provided function
``Has_Element`` is used. For example, the property stated above becomes:

.. code-block:: ada

   (for all C : Cursor => (if Has_Element (S, C) then P (Element (S, C))))

Like for the standard Ada iteration mechanism, it is possible to allow
quantification directly over the elements of the container by providing in
addition an ``Element`` primitive to the ``Iterable`` aspect. For example, if
we write:

.. code-block:: ada

   type Container is private with
     Iterable => (First       => First,
                  Next        => Next,
                  Has_Element => Has_Element
                  Element     => Element);

where

.. code-block:: ada

   function Element (S : Set; C : Cursor) return Element_Type;

then quantification over containers can be done directly on its elements. For
example, we could rewrite the above property into:

.. code-block:: ada

   (for all E of S => P (E))

For execution, quantification over elements of a container is translated as a
loop over its cursors. In the same way, for proof, quantification over elements
of a container is no more than syntactic sugar for quantification over its
cursors. For example, the above property is translated using quantification
over cursors :

.. code-block:: ada

   (for all C : Cursor => (if Has_Element (S, C) then P (Element (S, C))))

Depending on the application, this translation may be too low-level and
introduce an unnecessary burden on the automatic provers. As an example, let
us consider a package for functional sets:

.. code-block:: ada

  package Sets with SPARK_Mode is

    type Cursor is private;
    type Set (<>) is private with
      Iterable => (First       => First,
                   Next        => Next,
                   Has_Element => Has_Element,
                   Element     => Element);

    function Mem (S : Set; E : Element_Type) return Boolean with
      Post => Mem'Result = (for some F of S => F = E);

    function Intersection (S1, S2 : Set) return Set with
      Post => (for all E of Intersection'Result => Mem (S1, E) and Mem (S2, E))
        and (for all E of S1 =>
	         (if Mem (S2, E) then Mem (Intersection'Result, E)));

Sets contain elements of type ``Element_Type``. The most basic operation on sets
is membership test, here provided by the ``Mem`` subprogram. Every other
operation, such as intersection here, is then specified in terms of members.
Iteration primitives ``First``, ``Next``, ``Has_Element``, and ``Element``, that
take elements of a private type ``Cursor`` as an argument, are only provided for
the sake of quantification.

Following the scheme described previously, the postcondition of ``Intersection``
is translated for proof as:

.. code-block:: ada

  (for all C : Cursor =>
      (if Has_Element (Intersection'Result, C) then
             Mem (S1, Element (Intersection'Result, C))
         and Mem (S2, Element (Intersection'Result, C))))
  and
  (for all C1 : Cursor =>
      (if Has_Element (S1, C1) then
             (if Mem (S2, Element (S1, C1)) then
                   Mem (Intersection'Result, Element (S1, C1)))))

Using the postcondition of ``Mem``, this can be refined further into:

.. code-block:: ada

  (for all C : Cursor =>
      (if Has_Element (Intersection'Result, C) then
             (for some C1 : Cursor =>
                 Has_Element (S1, C1) and Element (Intersection'Result, C) = Element (S1, C1))
         and (for some C2 : Cursor =>
                 Has_Element (S2, C2) and Element (Intersection'Result, C) = Element (S2, C2))))
  and
  (for all C1 : Cursor =>
      (if Has_Element (S1, C1) then
             (if (for some C2 : Cursor =>
                 Has_Element (S2, C2) and Element (S1, C1) = Element (S2, C2)))
      then (for some C : Cursor => Has_Element (Intersection'Result, C)
               and Element (Intersection'Result, C) = Element (S1, C1))))

.. index:: Annotate; Iterable_For_Proof

Though perfectly valid, this translation may produce complicated proofs,
especially when verifying complex properties over sets. The |GNATprove|
annotation ``Iterable_For_Proof`` can be used to change the way ``for ... of``
quantification is translated. More precisely, it allows to provide |GNATprove|
with a `Contains` function, that will be used for quantification. For example,
on our sets, we could write:

.. code-block:: ada

  function Mem (S : Set; E : Element_Type) return Boolean;
  pragma Annotate (GNATprove, Iterable_For_Proof, "Contains", Mem);

With this annotation, the postcondition of ``Intersection`` is translated in a
simpler way, using logic quantification directly over elements:

.. code-block:: ada

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
last line of the postcondition of ``Init`` is translated for proof as:

.. code-block:: ada

  (for all C : Cursor =>
      (if Has_Element (Init'Result, C) then Element (Init'Result, C) = E));

Using the definition of ``Element`` and ``Has_Element``, it can then be refined
further into:

.. code-block:: ada

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

   function Model (L : List) return Sequence;
   pragma Annotate (GNATprove, Iterable_For_Proof, "Model", Entity => Model);

With this annotation, the postcondition of ``Init`` is translated directly as a
quantification on the elements of the result's model:

.. code-block:: ada

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

Inlining Functions for Proof
----------------------------

Contracts for functions are generally translated by |GNATprove| as axioms on
otherwise undefined functions. As an example, consider the following function:

.. code-block:: ada

    function Increment (X : Integer) return Integer with
      Post => Increment'Result >= X;

It will be translated by GNATprove as follows:

.. code-block:: ada

    function Increment (X : Integer) return Integer;

    axiom : (for all X : Integer. Increment (X) >= X);

For internal reasons due to ordering issues, expression functions are also
defined using axioms. For example:

.. code-block:: ada

    function Is_Positive (X : Integer) return Boolean is (X > 0);

will be translated exactly as if its definition was given through a
postcondition, namely:

.. code-block:: ada

    function Is_Positive (X : Integer) return Boolean;

    axiom : (for all X : Integer. Is_Positive (X) = (X > 0));

This encoding may sometimes cause difficulties to the underlying solvers,
especially for quantifier instantiation heuristics. This can cause strange
behaviors, where an assertion is proven when some calls to expression
functions are manually inlined but not without this inlining.

If such a case occurs, it is sometimes possible to instruct the tool to inline
the definition of expression functions using pragma ``Annotate``
``Inline_For_Proof``. When such a pragma is provided for an expression
function, a direct definition will be used for the function instead of an
axiom:

.. code-block:: ada

    function Is_Positive (X : Integer) return Boolean is (X > 0);
    pragma Annotate (GNATprove, Inline_For_Proof, Is_Positive);

The same pragma will also allow to inline a regular function, if its
postcondition is simply an equality between its result and an expression:

.. code-block:: ada

    function Is_Positive (X : Integer) return Boolean with
      Post => Is_Positive'Result = (X > 0);
    pragma Annotate (GNATprove, Inline_For_Proof, Is_Positive);

In this case, |GNATprove| will introduce a check when verifying the body of
``Is_Positive`` to make sure that the inline annotation is correct, namely, that
``Is_Positive (X)`` and ``X > 0`` always yield the same result. This check
may not be redundant with the verification of the postcondition of
``Is_Positive`` if the ``=`` symbol on booleans has been overridden.

Note that, since the translation through axioms is necessary for ordering
issues, this annotation can sometimes lead to a crash in GNATprove. It is the
case for example when the definition of the function uses quantification over a
container using the ``Iterable`` aspect.

.. index:: Annotate; Pledge

.. _Referring to a value at the end of a borrow:

Referring to a Value at the End of a Local Borrow
-------------------------------------------------

Local borrowers are objects of an anonymous access-to-variable type. At their
declaration, the ownership of (a part of) an existing data-structure is
temporarily transferred to the new object. The borrowed data-structure
will regain ownership afterward.

During the lifetime of the borrower, the borrowed object can be modified
indirectly through the borrower. It is forbidden to modify or even read the
borrowed object during the borrow. It can be problematic in some cases, for
example if a borrower is modified inside a loop, as GNATprove will need
information supplied in a loop invariant to know how the borrowed object and
the borrower are related in the loop and after it.

In assertions, we are still allowed to
express properties over a borrowed object using a `pledge`. The notion of
pledges was introduced by researchers from ETH Zurich to verify Rust programs
(see https://2019.splashcon.org/details/splash-2019-oopsla/31/Leveraging-Rust-Types-for-Modular-Specification-and-Verification).
Conceptually, a pledge is a property involving a borrower and/or the expression
it borrows which is known to hold at the end of the borrow, no matter
the modifications that may be done to the borrower. In |SPARK|, it is possible
to refer to the value of a local borrower or a borrowed expression at the
end of the borrow inside a regular assertion or contract, or as a parameter of
a call to a lemma function, using a function
annotated with the ``At_End_Borrow Annotate`` pragma:

.. code-block:: ada

   function At_End_Borrow (E : access constant T) return access constant T is
     (E)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

Note that the name of the function could be something other than
``At_End_Borrow``, but the annotation must use the string ``At_End_Borrow``.
|GNATprove| will check that a function associated with the ``At_End_Borrow``
annotation is a ghost expression function which takes a single parameter of an
access-to-constant type and returns it.

When |GNATprove| encounters a call to such a function, it checks that the
actual parameter of the call is rooted either at a local borrower or at an
expression which is borrowed in the current scope. It will not interpret it as
the current value of the expression, but rather as an imprecise value
representing the value that the expression could have at the end of the borrow.
As |GNATprove| does not do any forward look-ahead, nothing will be known about
the value of a local borrower at the end of the borrow, but the tool will still
be aware of the relation between this final value and the final value of the
expression it borrows.
As an example, let us consider a recursive type of doubly-linked lists:

.. code-block:: ada

    type List;
    type List_Acc is access List;
    type List is record
       Val  : Integer;
       Next : List_Acc;
    end record;

Using this type, let us construct a list ``X`` which stored the numbers form
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
     ...
   end;

While in the scope of ``Y``, the ownership of the list designated by ``X`` is
transferred to ``Y``, so that it is not allowed to access it from ``X``
anymore. After the end of the declare block, ownership is restored to ``X``,
which can again be accessed or modified directly.

Let us now define a function that can be used to relate the values
designated by ``X`` and ``Y`` at the end of the borrow:

.. code-block:: ada

   function At_End_Borrow (L : access constant List) return access constant List is
     (L)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

We can use this function to give properties that are known to hold during the
scope of ``Y``. Since ``Y`` and ``X`` designate the same value, we can
state in a pledge that the ``Val`` and ``Next`` components of ``X`` and ``Y``
always match:

.. code-block:: ada

      pragma Assert (At_End_Borrow (X).Val = At_End_Borrow (Y).Val);
      pragma Assert (At_End_Borrow (X).Next = At_End_Borrow (Y).Next);

However, even though at the beginning of the declare block, the first value of
``X`` is 1, it is not correct to assert that it will remain so inside a pledge:

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

Note that the pledge above is invalid even if ``Y.Val`` is `not` modified in the
following statements. A pledge is a contract about what
`is known to necessarily hold` in the
scope of ``Y``, not what will happen in practice. The analysis performed by
|GNATprove| remains a forward analysis, which is not impacted by
statements occurring after the current one.

Let us now consider a case where ``X`` is not borrowed completely. In the
declaration of ``Y``, we can decide to borrow only the last three elements of
the list:

.. code-block:: ada

   declare
      Y : access List := X.Next.Next;
   begin
      pragma Assert (At_End_Borrow (X.Next.Next).Val = At_End_Borrow (Y).Val);
      pragma Assert (At_End_Borrow (X.Next.Next) /= null);

      pragma Assert (At_End_Borrow (X.Next.Next.Val) = 3);
      -- incorrect, X could be modified through Y

      pragma Assert (At_End_Borrow (X.Next) /= null);
      pragma Assert (At_End_Borrow (X).Val = 1);
      -- rejected by the tool, X and X.Next are not part of a borrowed expression

      X.Val := 42;
   end;

Here, like in the previous example, we can state in a pledge that
``X.Next.Next.Val`` is ``Y.Val``, and then ``X.Next.Next`` cannot be set to
null. We also cannot assume anything about the
part of ``X`` designated by ``Y``, so we won't be able to prove that
``X.Next.Next.Val`` will remain 3. Note that we cannot get the value at the
end of the borrow of an expression which is not borrowed in the current scope.
Here, even if ``X.Next.Next`` is borrowed, ``X`` and ``X.Next`` are not. As
a result, calls to ``At_End_Borrow`` on them will be rejected by the tool.

Inside the scope of ``Y``, it is possible to modify the variable ``Y`` itself,
as opposed to modifying the structure it designates, so that it gives access to
a subcomponent of the borrowed structure. It is called a reborrow. In case of
reborrow, the pledge of the borrower is modified so that it
relates the expression borrowed initially to the new borrower. For
example, let's use ``Y`` to borrow ``X`` entirely and then modify it to only
designate ``X.Next.Next``:

.. code-block:: ada

   declare
      Y : access List := X;
   begin
      Y := Y.Next.Next;

      pragma Assert (At_End_Borrow (X).Next.Next /= null);
      pragma Assert (At_End_Borrow (X).Val = 1);
      pragma Assert (At_End_Borrow (X).Next.Val = 2);
      pragma Assert (At_End_Borrow (X).Next.Next.Val = 3);      --  incorrect
      pragma Assert (At_End_Borrow (X).Next.Next.Next /= null); --  incorrect
   end;

After the assignment, the part of ``X`` still accessible from the borrower is
reduced, but since ``X`` was borrowed entirely to begin with, the ownership
policy of |SPARK| still forbids direct access to any components of ``X`` while
in the scope of ``Y``. As a result, we have a bit more information about the
final value of ``X`` than in the previous case. We still know that ``X``
will hold at least three elements, that is ``X.Next.Next /= null``.
Additionally, the first and second components of ``X`` are no longer accessible
from ``Y``, and since they cannot be accessed directly through ``X``, we know
that they will keep their current values. This is why we can now assert in a
pledge that ``X.Val`` is 1 and ``X.Next.Val`` is 2.

However, we still cannot know anything
about the part of ``X`` still accessible from ``Y`` as these properties
could be modified later in the borrow:

.. code-block:: ada

      Y.Val := 42;
      Y.Next := null;

At_End_Borrow functions are also useful in postconditions of borrowing traversal
functions. A borrowing traversal function is a function which returns a local
borrower of its first parameter. As |GNATprove| works modularly on a per
subprogram basis, it is necessary to specify the pledge of the result of such
a function in its postcondition, or proof would not be able to recompute the
value of the borrowed parameter after the returned borrower goes out of scope.

As an example, we can define a ``Tail`` function which returns the ``Next``
component of a list if there is one, and ``null`` otherwise:

.. code-block:: ada

   function Tail (L : access List) return access List is
   begin
      if L = null then
         return null;
      else
         return L.Next;
      end if;
   end Tail;

In its postcondition, we want to consider the two cases, and, in each case,
specify both the value returned by the function and how the
parameter ``L`` is related to the returned borrower:

.. code-block:: ada

   function Tail (L : access List) return access List with
     Contract_Cases =>
       (L = null =>
          Tail'Result = null and At_End_Borrow (L) = null,
        others   => Tail'Result = L.Next
          and At_End_Borrow (L).Val = L.Val
          and At_End_Borrow (L).Next = At_End_Borrow (Tail'Result));

If ``L`` is ``null`` then ``Tail`` returns ``null`` and ``L`` will stay ``null``
for the duration of the borrow. Otherwise, ``Tail`` returns ``L.Next``, the
first element of ``L`` will stay as it was at the time of call, and the rest
of ``L`` stays equal to the object returned by ``Tail``.

Thanks to this postcondition, we can verify a program which borrows a part of
``L`` using the ``Tail`` function and modifies ``L`` through this borrower:

.. code-block:: ada

   declare
      Y : access List := Tail (Tail (X));
   begin
      Y.Val := 42;
   end;

   pragma Assert (X.Val = 1);
   pragma Assert (X.Next.Val = 2);
   pragma Assert (X.Next.Next.Val = 42);
   pragma Assert (X.Next.Next.Next.Val = 4);

Postconditions of borrowing traversal functions systematically need to provide two
properties: one specifying the result, and another specifying how the parameter is
related to the borrower. This is generally redundant, as the nature of a pledge
means the parameter/borrower relation always holds at the point of return of
the function. For example, on the post of 'Tail', ``Tail'Result = null`` and
``Tail'Result = L.Next`` repeat their respective pledge counterparts ``At_End_Borrow (L) = null``
and ``At_End_Borrow (L).Next = At_End_Borrow (Tail'Result)``.

The tool limit that redundancy by letting the user write only the parameter/borrower
relation. Properties of the result are automatically derived by
duplicating the post-condition, with calls to ``At_End_Borrow`` replaced by their
arguments. This covers most (if not all) properties of the result,
and additional properties of the result can be explicitly written if needed.
This means we get equivalent behavior for function ``Tail``
by writing the following more concise contract:

.. code-block:: ada

   function Tail (L : access List) return access List with
     Contract_Cases =>
       (L = null => At_End_Borrow (L) = null,
        others   => At_End_Borrow (L).Val = L.Val
          and At_End_Borrow (L).Next = At_End_Borrow (Tail'Result));


Accessing the Logical Equality for a Type
-----------------------------------------

In Ada, the equality is not the logical equality in general. In particular,
arrays are considered to be equal if they contain the same elements, even with
different bounds, +0.0 and -0.0 are considered equal...

It is possible to use a ``pragma Annotate (GNATprove, Logical_Equal)`` to ask
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
   type Dictionnary is array (Positive range <>) of Word;

   procedure Set (D : in out Dictionnary; I : Positive; W : String) with
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

It might happen that the underlying model of values of an Ada type contain
components which are not present in the Ada value. This makes it impossible to
implement a comparison function in Ada which would compute logical equality on
such types. This is the case in particular for arrays and discriminated
records with variant parts. More precisely, logical equality can be implemented
using the regular Ada equality for discrete types and fixed point types.
For floating point types, both the value and the sign need to be compared
(to tell the difference between +0.0 and -0.0). For pointers, as the address
is not modeled in SPARK, it is enough to check for nullity and compare the
designated value. Logical equality on untagged record with no variant parts can
be achieved by comparing the components. For other composite types, it cannot
be implemented and has to remain non-executable as in the example above.
Additionally, a user can safely annotate a comparison function on private types
whose full view is not in |SPARK| using the ``Logical_Equal`` annotation if it
behaves as expected, namely, it is an equivalence relation, and there is no way,
using the API provided in the public part of the enclosing package, to tell
the difference between two values on which this function returns True.

.. note::

   For private types whose full view is not in |SPARK|, |GNATprove| will peek
   inside the full view to try and determine whether or not to interpret the
   primitive equality on such types as the logical equality.

Note that, for types on which implementing the logical equality in Ada is
impossible, |GNATprove| might not be able to prove that two Ada values are
logically equal even if there is no way to tell the difference in |SPARK|.
For example, it might not be able to prove that two arrays
are logically equal even if they have the same bounds and the same value. It
is because it is not necessarily true in the underlying model, where values
outside of the array bounds are represented. Therefore, using an
assumption to state that two objects which are equal-in-Ada are logically equal
might introduce an unsoundness, in particular in the presence of slices. It is
demonstrated in the example below where |GNATprove| can prove that two strings
are not logically equal even though they have the same bounds and the same
elements. However, logical equality can be used safely as long as everything is
proved correct (no assumption is used).

.. code-block:: ada

   procedure Test is
      S1 : constant String := "foo1";
      S2 : constant String := "foo2";

   begin
      pragma Assert (S1 (1 .. 3) = S2 (1 .. 3));
      pragma Assert (not Real_Eq (S1 (1 .. 3), S2 (1 .. 3)));
   end Test;

Annotating a Private Type with Ownership
----------------------------------------

Private types whose full view is not in |SPARK| can be annotated with a
``pragma Annotate (GNATprove, Ownership, ...)``. Such a type is handled by
|GNATprove| in accordance to the :ref:`Memory Ownership Policy` of |SPARK|.
For example, the type ``T`` declared in the procedure ``Simple_Ownership``
below has an ownership annotation. As a result, |GNATprove| will reject the
second call to ``Read`` in the body of ``Simple_Ownership``, because the value
designated by ``X`` has been moved by the assignment to ``Y``.

.. literalinclude:: /examples/ug__ownership_annotations/simple_ownership.adb
   :language: ada
   :linenos:

In addition, it is possible to state that a type needs reclamation with a
``pragma Annotate (GNATprove, Onwership, "Needs_Reclamation", ...)``. In
this case, |GNATprove| emits checks to ensure that the resource is not leaked.
For these checks to be handled precisely, the user should annotate a function
taking a value of this type as a parameter and returning a boolean
with a ``pragma Annotate (GNATprove, Onwership, "Needs_Reclamation", ...)`` or
``pragma Annotate (GNATprove, Onwership, "Is_Reclaimed", ...)``. This
function will be used to check that the resource cannot be leaked. A function
annotated with ``"Needs_Reclamation"`` shall return True when its input holds
some resource while a function annotated with ``"Is_Reclaimed"`` shall return
True when its input has already been reclaimed. Only one such function shall
be provided for a given type. Two examples of use are given below.

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

Instantiating Lemma Procedures Automatically
--------------------------------------------

As featured in :ref:`Manual Proof Using User Lemmas`, it is possible to write
lemmas in |SPARK| as ghost procedures. However, actual calls to the procedure
need to be manually inserted in the program whenever an instance of the
lemma is necessary.
It is possible to use a pragma ``Annotate`` to instruct |GNATprove| that an
axiom should be introduced for a lemma procedure so manual
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

Using Annotations to Request Specialized Handling For Higher Order Functions
----------------------------------------------------------------------------

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
(see :ref:`Instantiating Lemma Procedures Automatically`) and its associated
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
