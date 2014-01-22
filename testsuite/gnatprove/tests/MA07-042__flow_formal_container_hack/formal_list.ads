with Ada.Containers.Formal_Vectors;

package Formal_List
is

   type Index_T is range 1 .. 100;

   function Eq (Left, Right : Integer) return Boolean is (Left = Right);

   package Vec is new Ada.Containers.Formal_Vectors
     (Index_Type   => Index_T,
      Element_Type => Integer,
      "="          => Eq);

   type T is private;

   type U is new Vec.Vector (100);

private

   type T is new Vec.Vector (100);

end Formal_List;
