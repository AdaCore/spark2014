package body Protected_Objects
  with SPARK_Mode
is
   protected body P1 is
      procedure Set (V : Natural) is
      begin
         The_Data := V;
      end Set;

      function Get return Natural is (The_Data);

      entry Reset when The_Data /= 0 is
      begin
         The_Data := 0;
      end Reset;

      procedure Signal is
      begin
         null;
      end Signal;
   end P1;

   protected body PT is
      procedure Set (V : Natural) is
      begin
         The_Data := V;
      end Set;

      function Get return Natural is (The_Data);

      entry Reset when The_Data /= 0 is
      begin
         The_Data := 0;
      end Reset;

      procedure Signal is
      begin
         null;
      end Signal;
   end PT;

end Protected_Objects;
