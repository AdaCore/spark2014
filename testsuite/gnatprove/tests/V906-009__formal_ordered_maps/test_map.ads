with SPARK.Containers.Formal.Ordered_Maps;
with Ada.Containers; use Ada.Containers;

package Test_Map with SPARK_Mode is

   package M is new SPARk.Containers.Formal.Ordered_Maps
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

   package N is new SPARk.Containers.Formal.Ordered_Maps
     (Element_Type    => Integer,
      Key_Type        => My_Rec,
      "<"             => My_Lt);

   procedure Test_Ordered_Map;

   procedure Large_Test;
end Test_Map;
