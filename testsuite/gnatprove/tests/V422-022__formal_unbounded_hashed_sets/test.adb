with SPARK.Containers.Formal.Unbounded_Hashed_Sets;
with Test_Set;
with Ada.Containers; use Ada.Containers;

procedure Test is
   function Id (N : Natural) return Hash_Type is
      (Hash_Type (N));

   package Sets is new SPARK.Containers.Formal.Unbounded_Hashed_Sets
     (Natural, Id);
begin
   Test_Set.Run_Test;
   Test_Set.Large_Test;
end Test;
