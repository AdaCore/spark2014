procedure P is
   procedure Test (X : in out Boolean) with Pre => True is
      Y : Boolean renames Boolean'(not X);
   begin
      X := not X;
      pragma Assert (Y /= X);  --@ASSERT:FAIL
   end;
   X : Boolean := True;
begin
   Test (X);
end;
