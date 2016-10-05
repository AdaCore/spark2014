pragma Ada_2012;
with Ada.Containers; use Ada.Containers;
with Ada.Containers.Indefinite_Vectors;

generic
   type Element_Type (<>) is private;
   No_Element : Element_Type;
   --  Special element which cannot be contained in any set. This is needed to
   --  use the Iterable aspect without introducing indirections (which would
   --  be bad for proof).

package Functional_Sets with SPARK_Mode is

   type Set is private with
     Default_Initial_Condition => Is_Empty (Set),
     Iterable                  => (First       => First_Element,
                                   Next        => Next_Element,
                                   Has_Element => Mem);
   --  Sets are empty when default initialized.
   --  For in quantification over sets iterates over elements.

   --  Sets are axiomatized using Mem which encodes whether an element is
   --  contained in a set. We could also add Length:

   function Mem (S : Set; E : Element_Type) return Boolean with
     Global => null,
     Post   => (if E = No_Element then not Mem'Result);
   pragma Annotate (GNATprove, Terminating, Mem);
   function Inc (S1, S2 : Set) return Boolean with
   --  Set inclusion.

     Global => null,
     Post   => Inc'Result = (for all E in S1 => Mem (S2, E));
   pragma Annotate (GNATprove, Terminating, Inc);
   function "=" (S1, S2 : Set) return Boolean with
   --  Extensional equality over sets.

     Global => null,
     Post   =>
       "="'Result = ((for all E in S1 => Mem (S2, E))
                     and (for all E in S2 => Mem (S1, E)));
   pragma Annotate (GNATprove, Terminating, Functional_Sets."=");
   pragma Warnings (Off, "unused variable");
   function Is_Empty (S : Set) return Boolean with
   --  A set is empty if it contains no element.

     Global => null,
     Post   => Is_Empty'Result = (for all E in S => False);
   pragma Warnings (On, "unused variable");
   pragma Annotate (GNATprove, Terminating, Is_Empty);
   function Is_Add (S : Set; E : Element_Type; Result : Set) return Boolean
   --  Returns True if Result is S augmented with E.

   with
     Global => null,
     Post   => Is_Add'Result =
       (E /= No_Element and Mem (Result, E) and not Mem (S, E)
        and (for all F in Result => Mem (S, F) or F = E)
        and (for all E in S => Mem (Result, E)));
   pragma Annotate (GNATprove, Terminating, Is_Add);
   function Add (S : Set; E : Element_Type) return Set with
   --  Returns S augmented with E.
   --  Is_Add (S, E, Result) should be used instead of Result = Add (S, E)
   --  whenever possible both for execution and for proof.

     Global => null,
     Pre    => E /= No_Element and then not Mem (S, E),
     Post   => Is_Add (S, E, Add'Result);
   pragma Annotate (GNATprove, Terminating, Add);
   function Is_Intersection (S1, S2, Result : Set) return Boolean with
   --  Returns True if Result is the intersection of S1 and S2.

     Global => null,
     Post   => Is_Intersection'Result =
       ((for all E in Result =>
               Mem (S1, E) and Mem (S2, E))
        and (for all E in S1 =>
               (if Mem (S2, E) then Mem (Result, E))));
   pragma Annotate (GNATprove, Terminating, Is_Intersection);
   function Intersection (S1, S2 : Set) return Set with
   --  Returns the intersection of S1 and S2.
   --  Intersection (S1, S2, Result) should be used instead of
   --  Result = Intersection (S1, S2) whenever possible both for execution and
   --  for proof.

     Global => null,
     Post   => Is_Intersection (S1, S2, Intersection'Result);

   function Is_Union (S1, S2, Result : Set) return Boolean with
   --  Returns True if Result is the union of S1 and S2.

     Global => null,
     Post   => Is_Union'Result =
       ((for all E in Result => Mem (S1, E) or Mem (S2, E))
        and (for all E in S1 => Mem (Result, E))
        and (for all E in S2 => Mem (Result, E)));
   pragma Annotate (GNATprove, Terminating, Is_Union);
   function Union (S1, S2 : Set) return Set with
   --  Returns the union of S1 and S2.
   --  Is_Union (S1, S2, Result) should be used instead of
   --  Result = Union (S1, S2) whenever possible both for execution and for
   --  proof.

     Global => null,
     Post   => Is_Union (S1, S2, Union'Result);

   --  For quantification purpose
   function First_Element (S : Set) return Element_Type;
   function Next_Element (S : Set; E : Element_Type) return Element_Type with
     Pre => Mem (S, E);
private
   pragma SPARK_Mode (Off);

   package Element_Lists is new Ada.Containers.Indefinite_Vectors
     (Element_Type => Element_Type,
      Index_Type   => Positive,
      "="          => "=");

   type Set is new Element_Lists.Vector with null record;

   --  We currently implement Set with Ada.Containers.Indefinite_Vectors
   --  but, ideally, we should rather use new indefinite vectors. Note that we
   --  should definitely not use limited types for those as we need to apply
   --  'Old on them.
end Functional_Sets;
