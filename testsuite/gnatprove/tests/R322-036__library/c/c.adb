package body C is

   procedure P is
      Old : constant Integer := A.Get;
   begin
      A.Mutate;
      pragma Assert (Old = A.Get); --@ASSERT:PASS
   end P;
end C;
