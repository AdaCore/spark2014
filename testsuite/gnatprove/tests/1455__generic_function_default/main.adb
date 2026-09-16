pragma Extensions_Allowed (On);

procedure Main with SPARK_Mode is

   generic
      with function Copy (X : Integer) return Integer is (X);
   procedure Test (X : Integer);

   procedure Test (X : Integer) is
   begin
      pragma Assert (Copy (X) = X); --@ASSERT:PASS
   end Test;

   procedure Default is new Test;

begin
   null;
end Main;
