with SPARK.Containers.Formal.Ordered_Sets;
with Test_Set;

procedure Test is
   package Sets_pkg is new SPARK.Containers.Formal.Ordered_Sets
     (Natural);
   use Sets_pkg;

   S : Set (10);
begin
   Insert (S, 2);
   Test_Set.Test_Ordered_Set;
   Test_Set.Large_Test;
   Test_Set.Large_Test_Key;
   null;
end Test;
