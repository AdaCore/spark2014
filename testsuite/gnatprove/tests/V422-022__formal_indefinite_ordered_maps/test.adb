with SPARK.Containers.Formal.Unbounded_Ordered_Maps;

procedure Test with SPARK_Mode is
   package Maps is new SPARK.Containers.Formal.Unbounded_Ordered_Maps
     (String, String);
   use Maps;

   M : Map;
   K1 : String := "1";
   K2 : String := "2";
   K3 : String := "3";

begin
   Insert (M, K1, "A");
   Insert (M, K2, "B");
   Insert (M, K3, "C");

   pragma Assert (Element (M, "2") = "B");
end Test;
