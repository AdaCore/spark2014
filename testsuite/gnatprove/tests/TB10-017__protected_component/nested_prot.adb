package body Nested_Prot with SPARK_Mode is
   protected body P1 is
      function Get return Integer is (C);
      entry Reset when C /= 0 is
      begin
         C := 0;
      end Reset;
      procedure Set (X : Integer) is
      begin
         C := X;
      end Set;
   end P1;

   protected body P2 is
      function Get return Integer is (C.Get);
      procedure Set (X : Integer) is
      begin
         C.Set (X);
      end Set;
      procedure Reset is
      begin
         C.Reset;
      end Reset;
   end P2;
end Nested_Prot;
