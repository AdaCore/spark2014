with SPARK.Containers.Formal.Unbounded_Hashed_Sets;
with Ada.Strings.Hash;

procedure Test with SPARK_Mode is
   package Sets is new SPARK.Containers.Formal.Unbounded_Hashed_Sets
     (String, Ada.Strings.Hash);
   use Sets;

   S : Set (Default_Modulus (4));

begin
   Insert (S, "A");
   Insert (S, "B");
   Insert (S, "C");

   pragma Assert (Contains (S, "B"));
end Test;
