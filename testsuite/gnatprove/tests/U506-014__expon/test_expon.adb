procedure Test_Expon with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);
   function Id (X : Float) return Float is (X);
begin
   pragma Assert (Id (2) ** 0 = Id (1));
   pragma Assert (Id (2) ** 1 = Id (2));
   pragma Assert (Id (2) ** 2 = Id (4));
   pragma Assert (Id (2) ** 3 = Id (8));
   pragma Assert (Id (2.0) ** (-1) = Id (0.5));
   pragma Assert (Id (2.0) ** (-2) = Id (0.25));
   pragma Assert (Id (2.0) ** (-3) = Id (0.125));
end Test_Expon;
