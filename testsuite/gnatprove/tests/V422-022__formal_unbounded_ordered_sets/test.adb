with SPARK.Containers.Formal.Unbounded_Ordered_Sets;
with Test_Set;

procedure Test is
   package Sets_pkg is new SPARK.Containers.Formal.Unbounded_Ordered_Sets
     (Natural);
   use Sets_pkg;

   S : Set;
begin
   Test_Set.Test_Ordered_Set;
   Test_Set.Large_Test;
   Test_Set.Large_Test_Key;
end Test;
