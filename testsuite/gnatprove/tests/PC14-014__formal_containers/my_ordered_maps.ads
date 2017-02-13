with Ada.Containers.Formal_Ordered_Maps;
with Ada.Containers; use Ada.Containers;

package My_Ordered_Maps with SPARK_Mode is

   package M is new Ada.Containers.Formal_Ordered_Maps
     (Element_Type    => Integer,
      Key_Type        => Natural,
      "<"             => "<");

   type My_Rec is record
      F : Integer;
      G : Integer;
   end record;

   function My_Lt (X, Y : My_Rec) return Boolean is (X.F < Y.F) with
   Post => My_Lt'Result = (X.F < Y.F);
   pragma Annotate (GNATprove, Inline_For_Proof, My_Lt);

   package N is new Ada.Containers.Formal_Ordered_Maps
     (Element_Type    => Integer,
      Key_Type        => My_Rec,
      "<"             => My_Lt);

   procedure Test_Ordered_Map;
end My_Ordered_Maps;
