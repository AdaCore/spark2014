with SPARK.Containers.Formal.Unbounded_Ordered_Maps;

procedure Test with SPARK_Mode is
   package Maps is new SPARK.Containers.Formal.Unbounded_Ordered_Maps
     (String, String);
   use Maps; use Maps.Formal_Model; use Maps.Formal_Model.M;

   M : Maps.Map;
   K1 : String := "1";
   K2 : String := "2";
   K3 : String := "3";
   E2 : String := "B";

begin
   pragma Assert (not Equivalent_Keys (K1, K2));
   pragma Assert (not Equivalent_Keys (K1, K3));
   pragma Assert (not Equivalent_Keys (K2, K3));
   Insert (M, K1, "A");
   Insert (M, K2, E2);
   Insert (M, K3, "C");
   declare
      L2 : String := "2";
   begin
      pragma Assert (Equivalent_Keys (K2, L2));
      pragma Assert (Element (M, L2) = E2);
   end;
end Test;
