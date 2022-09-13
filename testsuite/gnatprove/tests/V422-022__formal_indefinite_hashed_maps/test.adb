with SPARK.Containers.Formal.Unbounded_Hashed_Maps;
with Ada.Strings.Hash;


procedure Test with SPARK_Mode is
   package Maps is new SPARK.Containers.Formal.Unbounded_Hashed_Maps
    (String, String, Ada.Strings.Hash);
   use Maps;

   M : Map (Default_Modulus (4));

   K1 : String := "1";
   K2 : String := "2";
   K3 : String := "3";

begin
   Insert (M, K1, "A");
   Insert (M, K2, "B");
   Insert (M, K3, "C");

   pragma Assert (Element (M, K2) = "B");

end Test;
