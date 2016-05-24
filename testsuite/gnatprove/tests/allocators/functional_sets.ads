pragma Ada_2012;
with Conts;          use Conts;
with Conts.Vectors.Indefinite_Unbounded;

generic
   type Element_Type (<>) is private;
   with function "=" (Left, Right : Element_Type) return Boolean is <>;
package Functional_Sets with SPARK_Mode is

   type Set is private with
     Default_Initial_Condition => Is_Empty (Set),
     Iterable                  => (First       => Iter_First,
                                   Next        => Iter_Next,
                                   Has_Element => Iter_Has_Element,
                                   Element     => Iter_Element);
   --  Sets are empty when default initialized.
   --  For in quantification over sets should not be used.
   --  For of quantification over sets iterates over elements.

   --  Sets are axiomatized using Mem which encodes whether an element is
   --  contained in a set. We could also add Length.
   --  ??? Currently we do not consider potential overflows of the container's
   --  implementation.

   function Mem (S : Set; E : Element_Type) return Boolean with
     Global => null;

   function Inc (S1, S2 : Set) return Boolean with
   --  Set inclusion.

     Global => null,
     Post   => Inc'Result = (for all E of S1 => Mem (S2, E));

   function "=" (S1, S2 : Set) return Boolean with
   --  Extensional equality over sets.

     Global => null,
     Post   =>
       "="'Result = ((for all E of S1 => Mem (S2, E))
                     and (for all E of S2 => Mem (S1, E)));

   pragma Warnings (Off, "unused variable");
   function Is_Empty (S : Set) return Boolean with
   --  A set is empty if it contains no element.

     Global => null,
     Post   => Is_Empty'Result = (for all E of S => False);
   pragma Warnings (On, "unused variable");

   function Is_Add (S : Set; E : Element_Type; Result : Set) return Boolean
   --  Returns True if Result is S augmented with E.

   with
     Global => null,
     Post   => Is_Add'Result =
       (Mem (Result, E) and not Mem (S, E)
        and (for all F of Result => Mem (S, F) or F = E)
        and (for all E of S => Mem (Result, E)));

   function Add (S : Set; E : Element_Type) return Set with
   --  Returns S augmented with E.
   --  Is_Add (S, E, Result) should be used instead of Result = Add (S, E)
   --  whenever possible both for execution and for proof.

     Global => null,
     Pre    => not Mem (S, E),
     Post   => Is_Add (S, E, Add'Result);

   function Remove (S : Set; E : Element_Type) return Set with
   --  Returns S without E.
   --  Is_Add (Result, E, S) should be used instead of S = Add (Result, E)
   --  whenever possible both for execution and for proof.

     Global => null,
     Pre    => Mem (S, E),
     Post   => Is_Add (Remove'Result, E, S);

   function Is_Intersection (S1, S2, Result : Set) return Boolean with
   --  Returns True if Result is the intersection of S1 and S2.

     Global => null,
     Post   => Is_Intersection'Result =
       ((for all E of Result =>
               Mem (S1, E) and Mem (S2, E))
        and (for all E of S1 =>
               (if Mem (S2, E) then Mem (Result, E))));

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
       ((for all E of Result => Mem (S1, E) or Mem (S2, E))
        and (for all E of S1 => Mem (Result, E))
        and (for all E of S2 => Mem (Result, E)));

   function Union (S1, S2 : Set) return Set with
   --  Returns the union of S1 and S2.
   --  Is_Union (S1, S2, Result) should be used instead of
   --  Result = Union (S1, S2) whenever possible both for execution and for
   --  proof.

     Global => null,
     Post   => Is_Union (S1, S2, Union'Result);

   --  For quantification purpose
   --  Do not use them in practice
   --  ??? Is there a way to prevent users from using those ?
   type Private_Key is private;

   function Iter_First (S : Set) return Private_Key with
     Global => null;
   function Iter_Has_Element (S : Set; K : Private_Key) return Boolean with
     Global => null;
   function Iter_Next (S : Set; K : Private_Key) return Private_Key with
     Global => null,
     Pre    => Iter_Has_Element (S, K);
   function Iter_Element (S : Set; K : Private_Key) return Element_Type with
     Global => null,
     Pre    => Iter_Has_Element (S, K);
   pragma Annotate (GNATprove, Iterable_For_Proof, "Contains", Mem);
private
   pragma SPARK_Mode (Off);

   type Neither_Controlled_Nor_Limited is tagged null record;

   --  Functional sets are neither controlled nor limited. As a result,
   --  no primitive should be provided to modify them. Note that we
   --  should definitely not use limited types for those as we need to apply
   --  'Old on them.
   --  ??? Should we make them controlled to avoid memory leak ?

   package Element_Lists is new Conts.Vectors.Indefinite_Unbounded
     (Element_Type        => Element_Type,
      Index_Type          => Count_Type,
      Container_Base_Type => Neither_Controlled_Nor_Limited);

   type Set is new Element_Lists.Vector with null record;

   type Private_Key is new Element_Lists.Cursor;
end Functional_Sets;
