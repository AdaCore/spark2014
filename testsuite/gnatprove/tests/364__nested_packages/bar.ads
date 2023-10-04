package Bar with SPARK_Mode is
   package Ok is
      function Id (X : Integer) return Integer is (X);
      subtype My_Int is Integer range Id (1) .. Id (10);
      A : constant My_Int := Id (10);

      package Nested is
         B : constant Integer := A;
         C : constant My_Int := Id (10);
         pragma Assert (B = 10); -- @ASSERT:PASS
      end Nested;

      D : constant Integer := Nested.C;
      pragma Assert (D = 10); -- @ASSERT:PASS
   end Ok;

   package Bad is
      function Id (X : Integer) return Integer is (X);
      subtype My_Int is Integer range Id (1) .. Id (5);
      A : constant My_Int := Id (10);  --  @RANGE_CHECK:FAIL

      package Nested is
         B : constant Integer := A;
         C : constant My_Int := Id (10);
      end Nested;

      D : constant Integer := Nested.C;
   end Bad;
end Bar;
