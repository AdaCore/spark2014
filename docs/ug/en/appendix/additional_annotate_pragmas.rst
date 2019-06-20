
.. _Uses_of_Pragma_Annotate_GNATprove:

Uses of Pragma Annotate GNATprove
=================================

This appendix lists all the uses of pragma ``Annotate`` for |GNATprove|.
Pragma ``Annotate`` can also be used to control other AdaCore tools. The uses
of this pragma are explained in the User's guide of each tool.

The main usage of pragmas ``Annotate`` for |GNATprove| is for justifying check
messages using :ref:`Direct Justification with Pragma Annotate`. Specific
versions of this pragma can also be used to influence the generation of proof
obligations. Some of these uses can be seen in :ref:`SPARK Libraries` for
example. These forms of pragma ``Annotate`` should be used with care as they
can introduce additional assumptions which are not verified by the |GNATprove|
tool.

Using Pragma Annotate to Justify Check Messages
-----------------------------------------------

You can use annotations of the form

.. code-block:: ada

    pragma Annotate (GNATprove, False_Positive,
                     "message to be justified", "reason");

to justify an unproved check message that cannot be proved by other means. See
the section :ref:`Direct Justification with Pragma Annotate` for more details
about this use of pragma ``Annotate``.

Using pragma Annotate to force Proof of Termination
---------------------------------------------------

SPARK doesn't usually prove termination of subprograms. You can instruct it do
so using annotations of this form:

.. code-block:: ada

   pragma Annotate (GNATprove, Terminating, Subp_Or_Package_Entity);

See the section :ref:`Subprogram Termination` about details of this use of
pragma ``Annotate``.

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

   (for all C : Cursor => (if Has_Element (S, C) then P (Element (S, C)))

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

   (for all C : Cursor => (if Has_Element (S, C) then P (Element (S, C)))

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
                   Has_Element (S2, C2) and Element (Intersection'Result, C) = Element (S2, C2)))))
  and
  (for all C1 : Cursor =>
      (if Has_Element (S1, C1) then
             (if (for some C2 : Cursor =>
                 Has_Element (S2, C2) and Element (S1, C1) = Element (S2, C2)))
      then (for some C : Cursor =>  Has_Element (Intersection'Result, C)
               and Element (Intersection'Result, C) = Element (S1, C1))))))

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

.. _Inlining_Functions_for_Proof:

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
