with SPARK.Containers.Formal.Ordered_Sets;

procedure Test with SPARK_Mode is
   function Key (X : Natural) return Natural is
      (X);

   package Sets is new SPARK.Containers.Formal.Ordered_Sets (Natural);
   use Sets;
   package Keys is new Sets.Generic_Keys (Natural, Key);
   use Keys;

   S : Set (10);
begin
   Insert (S, 3);
   Insert (S, 4);

   Replace (S, 3, 5);
end Test;
