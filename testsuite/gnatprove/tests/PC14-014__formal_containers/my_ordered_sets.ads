with Ada.Containers.Formal_Ordered_Sets;
with Ada.Containers; use Ada.Containers;

package My_Ordered_Sets with SPARK_Mode is

   package M is new Ada.Containers.Formal_Ordered_Sets
     (Element_Type => Natural);

   type My_Rec is record
      F : Natural;
      G : Integer;
   end record;

   function My_Lt (X, Y : My_Rec) return Boolean is (X.F < Y.F) with
   Post => My_Lt'Result = (X.F < Y.F);
   pragma Annotate (GNATprove, Inline_For_Proof, My_Lt);

   package N is new Ada.Containers.Formal_Ordered_Sets
     (Element_Type => My_Rec,
      "<"          => My_Lt);

   function Get_F (X : My_Rec) return Positive is (X.F)
   with Post => Get_F'Result = X.F;
   pragma Annotate (GNATprove, Inline_For_Proof, Get_F);

   package G is new N.Generic_Keys
     (Key_Type => Positive,
      Key      => Get_F,
      "<"      => "<");

   procedure Test_Ordered_Set;
end My_Ordered_Sets;
