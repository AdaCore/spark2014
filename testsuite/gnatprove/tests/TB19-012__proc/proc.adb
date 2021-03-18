procedure Proc is

   X : Integer := 0;
   Y : Integer := 0 with Address => X'Address;

   procedure Inc (A : in out Integer) with Pre => A < Integer'Last;
   procedure Inc (A : in out Integer) is
   begin
      A := A + 1;
   end Inc;

begin
   pragma Assert (X = 0); --@ASSERT:FAIL
   Inc (Y);
   pragma Assert (X = 0); --@ASSERT:FAIL
end Proc;
