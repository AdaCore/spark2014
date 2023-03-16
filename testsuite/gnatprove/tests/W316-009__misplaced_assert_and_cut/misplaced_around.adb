procedure Misplaced_Around with SPARK_Mode is
   package A is
      B : constant Boolean := False;
      pragma Assert_And_Cut (B);
   end A;
   procedure Hide is
      X : Integer := 0;
      package B is
         pragma Assert_And_Cut (1 / X = 0);
      end B;
   begin
      null; 
   end Hide;
   function Rand return Boolean with Import, Global => null;
begin
   if Rand then
      pragma Assert (A.B);
   else
      pragma Assert (not A.B);
   end if;
end Misplaced_Around;
