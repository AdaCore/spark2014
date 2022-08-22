with SPARK.Containers.Formal.Hashed_Maps;
with Ada.Containers; use Ada.Containers;

with Test_Map;

procedure Test is
   function Id (N : Positive) return Hash_Type is
      (Hash_Type (N));

   package Maps is new SPARK.Containers.Formal.Hashed_Maps
     (Key_Type     => Positive,
      Element_Type => Natural,
      Hash         => Id);
begin
   Test_Map.Run_Test;
   Test_Map.Large_Test;
end Test;
