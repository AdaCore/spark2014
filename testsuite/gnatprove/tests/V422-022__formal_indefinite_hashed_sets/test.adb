with SPARK.Containers.Formal.Unbounded_Hashed_Sets;
with SPARK.Containers.Hash;

procedure Test with SPARK_Mode is
   package Sets is new SPARK.Containers.Formal.Unbounded_Hashed_Sets
     (String, SPARK.Containers.Hash.String_Hash, Hash_Equivalent => SPARK.Containers.Hash.String_Hash_Equivalent);
   use Sets;

   S : Set;

begin
   Insert (S, "A");
   Insert (S, "B");
   Insert (S, "C");

   pragma Assert (Contains (S, "B"));
end Test;
