with SPARK.Containers.Formal.Unbounded_Ordered_Sets;

procedure Test with SPARK_Mode is
   package Sets is new SPARK.Containers.Formal.Unbounded_Ordered_Sets
     (String);
   use Sets;

   S : Set;
   K1 : String := "1";
   k2 : String := "2";
   k3 : String := "3";
begin
   Insert (S, K1);
   Insert (S, K2);
   Insert (S, K3);

   pragma Assert (Contains (S, K2));
end Test;
