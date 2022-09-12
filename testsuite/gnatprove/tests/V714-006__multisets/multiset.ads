pragma Ada_2012;
private with SPARK.Containers.Functional.Maps;

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

with Ada.Containers;
use Ada.Containers;

package Multiset with
  SPARK_Mode => On,
  Annotate => (GNATprove, Always_Return)
is
   type Element_Type is new Natural;


   type Multiset is private with
     Default_Initial_Condition => Is_Empty (Multiset),
     Iterable                  => (First       => Iter_First,
                                   Next        => Iter_Next,
                                   Has_Element => Iter_Has_Element,
                                   Element     => Iter_Element);


   function Is_Empty (Container : Multiset) return Boolean with
   --  A Multiset is empty if it has no Element. In other words, if the number
   --  of occurence of all the element is 0.

     Global => null,
     Post   => Is_Empty'Result = (for all Element of Container => False)
                 and then Is_Empty'Result = (Cardinality (Container) = 2); --@POSTCONDITION:FAIL

   function Cardinality (Container : Multiset) return Big_Natural with
   --  The Cardinality of a Multiset is the nulber of Element in the Multiset
   --  taking into account the number of occurence.

     Global => null;
     --  Post   => (if Is_Empty (Container) then Cardinality'Result = 0);

   function Nb_Occurence
     (Container : Multiset;
      Element   : Element_Type) return Big_Natural with
   --  Get the number of occurence of Element in the Container.

     Global => null;

   function Contains
     (Container : Multiset;
      Element   : Element_Type) return Boolean with
   --  An Element is a  if a Multiset if it occure at least once in it

     Global => null,
     Post   => Contains'Result = (Nb_Occurence (Container, Element) > 0),
     Annotate => (GNATprove, Inline_For_Proof);

   function Choose (Container : Multiset) return Element_Type with
     Global => null,
     Pre    => not Is_Empty (Container),
     Post   => Contains (Container, Choose'Result);

   type Private_Key is private;

   function Iter_First (Container : Multiset) return Private_Key with
     Global => null;

   function Iter_Has_Element
     (Container : Multiset;
      Key       : Private_Key) return Boolean
   with
     Global => null;

   function Iter_Next (Container : Multiset; Key : Private_Key)
                       return Private_Key
   with
     Global => null,
     Pre    => Iter_Has_Element (Container, Key);

   function Iter_Element
     (Container : Multiset;
      Key       : Private_Key) return Element_Type
   with
     Global => null,
     Pre    => Iter_Has_Element (Container, Key);
   pragma Annotate (GNATprove, Iterable_For_Proof, "Contains", Contains);

private

   package Maps is new SPARK.Containers.Functional.Maps
     (Key_Type     => Element_Type,
      Element_Type => Big_Positive);
   use Maps;

   function Choose (M : Map) return Element_Type with
     Import,
     Global => null,
     Pre => not Is_Empty (M),
     Post => Has_Key (M, Choose'Result);

   ------------
   -- Lemmas --
   ------------

   function Cardinality_Rec (Container : Maps.Map) return Big_Natural with
     Ghost,
     Subprogram_Variant => (Decreases => Maps.Length (Container));

   type Multiset is record
      Map  : Maps.Map;
      Card : Big_Natural := 0;
   end record with
     Type_Invariant => Invariant (Multiset);

   function Invariant (Container : Multiset) return Boolean with Ghost;

   type Private_Key is new Maps.Private_Key;

   function Iter_First (Container : Multiset) return Private_Key is
     (Iter_First (Container.Map));

   function Iter_Has_Element
     (Container : Multiset;
      Key       : Private_Key) return Boolean
   is
     (Iter_Has_Element (Container.Map, Key));

   function Iter_Next
     (Container : Multiset;
      Key       : Private_Key) return Private_Key
   is
     (Iter_Next (Container.Map, Key));

   function Iter_Element
     (Container : Multiset;
      Key       : Private_Key) return Element_Type
   is
     (Iter_Element (Container.Map, Key));

end Multiset;
