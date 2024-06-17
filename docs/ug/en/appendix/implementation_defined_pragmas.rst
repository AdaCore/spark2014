Implementation Defined Aspects and Pragmas
==========================================

This appendix lists all the aspects or pragmas specific to |GNATprove|.

.. index:: SPARK_Mode; rules

.. _Pragma_SPARK_Mode:

Aspect and Pragma ``SPARK_Mode``
--------------------------------

SPARK_Mode is a three-valued aspect. At least until we get to the
next paragraph, a SPARK_Mode of On, Off, or Auto is associated
with each Ada construct. Roughly, the meaning of the three values is the
following:

 * a value of On means that the construct is required to be in |SPARK|, and
   the construct will be analyzed by |GNATprove|.
 * a value of Off means that the construct will not be analyzed by
   |GNATprove|, and does not need to obey the |SPARK| restrictions. The
   construct also cannot be referenced from other parts that are required to
   be in |SPARK|.
 * a value of Auto means that the construct will not be analyzed, and
   |GNATprove| will infer whether this construct can be used in other |SPARK|
   parts or not.

As generic units are not directly analyzed by |GNATprove|, but only generic
instances are, the meaning of the three values is slightly different for
generic units:

 * a value of On means that instances can be in |SPARK|, depending on the
   parameters passed for the instantiation.
 * a value of Off means that instances cannot be in |SPARK|, independent of the
   parameters passed for the instantiation.
 * a value of Auto provides no information on whether instances can be in
   |SPARK| or not.

We now explain in more detail how the SPARK_Mode pragma works.

Some Ada constructs are said to have more than one "section".
For example, a declaration which requires a completion will have (at least)
two sections: the initial declaration and the completion. The SPARK_Modes
of the different sections of one entity may differ. In other words,
SPARK_Mode is not an aspect of an entity but rather of a section of an entity.

For example, if a subprogram declaration has a SPARK_Mode of On while
its body has a SPARK_Mode of Off, then an error would be generated if
the subprogram  took a parameter of a general access type but not if
the subprogram declared a local variable of a general
access type (recall that general access types are not in |SPARK|).

A package is defined to have 4 sections: its visible part, its private part,
its body declarations, and its body statements. A protected or task unit has
3 sections: its visible part, its private part, and its body.
Other declarations which require a completion have two sections, as noted
above; all other entities and constructs have only one section.

If the SPARK_Mode of a section of an entity is Off, then the SPARK_Mode
of a later section of that entity shall not be On. [For example, a subprogram
can have a SPARK declaration and a non-SPARK body, but not vice versa.]

If the SPARK_Mode of a section of an entity is Auto, then the SPARK_Mode
of a later section of that entity shall not be On, and it shall not be Off
unless that entity is a generic entity, or an instance of such a generic.
[This makes it possible to mark a later section of a generic unit as Off,
in cases where its initial section is Auto to allow instantiations to
have any value of SPARK_Mode.]

The SPARK_Mode aspect can be specified either via a pragma or via an
aspect_specification. In some contexts, only a pragma can be used
because of syntactic limitations. In those contexts where an
aspect_specification can be used, it has the same effect as a
corresponding pragma.

The form of a pragma SPARK_Mode is as follows:

.. code-block:: ada

   pragma SPARK_Mode [ (On | Off) ]

The form for the aspect_definition of a SPARK_Mode aspect_specification is
as follows:

.. code-block:: ada

   [ On | Off ]

For example:

.. code-block:: ada

   package P
      with SPARK_Mode => On
   is

The pragma can be used as a configuration pragma. The effect of
such a configuration pragma is described below in the rules for
determining the SPARK_Mode aspect value for an arbitrary section of an
arbitrary Ada entity or construct.

Pragma ``SPARK_Mode`` shall be used as a local pragma in only the following
contexts and has the described semantics:

.. csv-table::
   :header: "Pragma placement", "Affected construct", "Alternative aspect form"
   :widths: 3, 1, 1

   "Start of the visible declarations (preceded only by other pragmas) of a
   package declaration", "Visible part of the package", "As part of the
   package_specification"
   "Start of the visible declarations (preceded only by other pragmas) of a task
   or protected unit", "Visible part of the unit", "As part of the declaration"
   "Start of the private declarations of a package, a protected unit, or a task
   unit (only other pragmas can appear between the ``private`` keyword and the
   ``SPARK_Mode`` pragma)", "Private part", "None"
   "Immediately at the start of the declarations of a package body (preceded only
   by other pragmas)", "Body declarations of the package", "As part of the
   package_body"
   "Start of the elaboration statements of a package body (only other pragmas can
   appear between the ``begin`` keyword and the ``SPARK_Mode`` pragma)", "Body
   statements of the package", "None"
   "Start of the declarations of a protected or task body (preceded only by other
   pragmas)", "Body", "As part of the protected or task body"
   "After a subprogram declaration (with only other pragmas intervening). [This
   does not include the case of a subprogram whose initial declaration is via a
   subprogram_body_stub. Such a subprogram has only one section because a subunit
   is not a completion.]", "Subprogram's specification", "As part of the
   subprogram_declaration"
   "Start of the declarations of a subprogram body (preceded only by other
   pragmas)", "Subprogram's body", "As part of the subprogram_body"

A default argument of On is assumed for any SPARK_Mode pragma or
aspect_specification for which no argument is explicitly specified.

A SPARK_Mode of Auto can only be explicitly specified for a configuration
pragma; the cases in which a SPARK_Mode of Auto is implicitly specified are
described below. Roughly speaking, Auto indicates that it is left up to the
formal verification tools to determine whether or not a given construct is in
|SPARK|.

A SPARK_Mode pragma or aspect specification shall only apply to a
(section of a) package, generic package, subprogram, or
generic subprogram.

A SPARK_Mode of On shall only apply to a (section of a) library-level entity,
except for the case of SPARK_Mode specifications occurring within generic
instances. A SPARK_Mode of On applying to a non-library-level entity within a
generic instance has no effect.

The SPARK_Mode aspect value of an arbitrary section of an arbitrary
Ada entity or construct is then defined to be the following value
(except if this yields a result of Auto for a non-package; see below):

- If SPARK_Mode has been specified for the given section of the
  given entity or construct, then the specified value;

- else for the instance of a generic unit, follow the rules as for a
  declaration that would not be a generic instantiation; take the resulting
  value of SPARK_Mode if it is Auto or Off; otherwise, take the value of
  SPARK_Mode specified for the generic unit if any; otherwise the value is On.

- else for the private part of a public child unit whose parent unit's
  private part has a SPARK_Mode of Off, the SPARK_Mode is Off;

- else for the private part of a package or a protected or task unit,
  the SPARK_Mode of the visible part;

- else for a package body's statements, the SPARK_Mode of the
  package body's declarations;

- else for the first section (in the case of a package, the visible part)
  of a public child unit, the SPARK_Mode of the visible part of the
  parent unit;

- else for the first section (in the case of a package, the visible part)
  of a private child unit, the SPARK_Mode of the private part of the
  parent unit;

- else for any of the visible part or body declarations of a library
  unit package or either section of a library unit subprogram,
  if there is an applicable SPARK_Mode configuration pragma then the
  value specified by the pragma; if no such configuration pragma
  applies, then an implicit specification of Auto is assumed;

- else the SPARK_Mode of the enclosing section of the nearest enclosing
  package or subprogram;

- Corner case: the SPARK_Mode of the visible declarations of the
  limited view of a package is always Auto.

If the above computation yields a result of Auto for any construct
other than one of the four sections of a package, then a result of On
or Off is determined instead based on the legality (with respect to
the rules of |SPARK|) of the construct. The construct's SPARK_Mode is
On if and only if the construct is in |SPARK|. [A SPARK_Mode of Auto
is therefore only possible for (sections of) a package.]

In code where SPARK_Mode is On (also called "SPARK code"), the rules of
|SPARK| are enforced. In particular, such code shall not reference
non-SPARK entities, although such code may reference a SPARK declaration
with one or more non-SPARK subsequent sections (e.g., a package whose
visible part has a SPARK_Mode of On but whose private part has a SPARK_Mode
of Off; a package whose visible part has a SPARK_Mode of Auto may also be
referenced).

Code where SPARK_Mode is Off shall not enclose code where Spark_Mode is On.
However, if an instance of a generic unit is enclosed
by code where SPARK_Mode is Off and if any SPARK_Mode specifications occur
within the generic unit, then the corresponding SPARK_Mode specifications
occurring within the instance have no semantic effect. [In particular,
such an ignored SPARK_Mode specification could not violate the preceding
"Off shall not enclose On" rule because the SPARK_Mode of the
entire instance is Off. Similarly, such an ignored SPARK_Mode specification
could not violate the preceding rule that a SPARK_Mode specification
shall only apply to a (section of a) library-level entity.]

For purposes of the "Off shall not enclose On" rule just described, the
initial section of a child unit is considered to occur immediately
within either the visible part (for a public child unit) or the private
part (for a private child unit) of the parent unit. In addition, the private
part of a public child package is considered to occur immediately
within the private part of the parent unit. [This follows Ada's visibility
rules for child units. This means, for example, that if a parent unit's
private part has a SPARK_Mode of Off, then the private part of a
public child package shall not have a SPARK_Node of On. Note also that
a SPARK_Mode configuration pragma which applies only to the specification
(not the body) of a child unit is always ineffective; this is a consequence
of the rules given above for determining the SPARK_Mode of the first
section of a child unit.]

The rules for a protected
unit follow from the rules given for other constructs after notionally
rewriting the protected unit as a package.

A protected unit declaration such as

.. code-block:: ada

   protected type Prot
     with SPARK_Mode => On
   is
      procedure Op1 (X : in out Integer);
      procedure Op2;
      function Non_SPARK_Profile (X : in out Integer) return Boolean
        with SPARK_Mode => Off;
   private
      Aaa, Bbb : Integer := 0;
   end Prot;

can be thought of, for purposes of SPARK_Mode rules, as being
a lot like

.. code-block:: ada

   package Pkg
     with SPARK_Mode => On
   is
      type Prot is limited private;
      procedure Op1 (Obj : in out Prot; X : in out Integer);
      procedure Op2 (Obj : in out Prot);
      function Non_SPARK_Profile (Obj : Prot; Ptr : in out Integer) return Boolean
        with SPARK_Mode => Off;
   private
      type Prot is
        limited record
           Aaa, Bbb : Integer := 0;
        end record;
   end Pkg;

which is legal. The point is that a protected type which is
in |SPARK| can have protected operation whose declaration is not in |SPARK|.

SPARK_Mode is an implementation-defined Ada aspect; it is not (strictly
speaking) part of the |SPARK| language. It is used to notionally transform
programs which would otherwise not be in |SPARK| so that they can
be viewed (at least in part) as |SPARK| programs.

Note that if you would like to mark all your code in SPARK_Mode, the
simplest solution is to specify in your project file::

   package Compiler is
      for Local_Configuration_Pragmas use "spark.adc";
   end Compiler;

and provide a file `spark.adc` which contains::

   pragma SPARK_Mode;

.. index:: Annotate; Iterable; Iterable_For_Proof

.. _Aspect and Pragma Iterable:

Aspect and Pragma ``Iterable``
------------------------------

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
