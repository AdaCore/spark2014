--  A simple bitset package written in SPARK.
--  For the imperative interface, it seems to be necessary to fix the size to a
--  previously decided constant.
--  For a purely functional interface, one could use unconstrained arrays
--  instead, where "elt not in S'Range" means "S(Elt) + False"

generic
   Max : Positive;
package Bitsets is

   type Element is new Positive range 1 .. Max;

   type Set is private;

   function Mem (S : Set; E : Element) return Boolean;

   function Add (S : Set; E : Element) return Set
     with Post =>
       (for all Elt in Element =>
          Mem (Add'Result, Elt) = (if Elt = E then True else Mem (S, Elt)));

   function Remove (S : Set; E : Element) return Set
     with Post =>
       (for all Elt in Element =>
          Mem (Remove'Result, Elt) =
        (if Elt = E then False else Mem (S, Elt)));

   function Union (A, B : Set) return Set
     with Post =>
       (for all Elt in Element =>
          Mem (Union'Result, Elt) = (Mem (A, Elt) or else Mem (B, Elt)));

   function Empty return Set
     with Post => (for all Elt in Element => not Mem (Empty'Result, Elt));

   function Ext_Equal (A, B : Set) return Boolean
   is (for all Elt in Element =>
          Mem (A, Elt) = Mem (B, Elt));


   procedure Add (S : in out Set; E : Element)
     with Post => Ext_Equal (S, Add (S'Old, E));

   procedure Remove (S : in out Set; E : Element)
     with Post => Ext_Equal (S, Remove (S'Old, E));

   procedure Union (A : in out Set; B : Set)
     with Post => Ext_Equal (A, Union (A'Old, B));

private

   type Set is array (Element) of Boolean
     with Pack;

end Bitsets;
