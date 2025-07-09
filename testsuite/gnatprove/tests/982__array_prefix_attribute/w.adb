procedure W is
   type A is array (1 .. 1) of Integer;
   type B is array (1 .. 1) of A;
   procedure Test (X : B; Y : access constant B; J : Integer) with Pre => True is
      First  : constant Integer := X (1 / J)'First;   --@DIVISION_CHECK:FAIL
      Last   : constant Integer := X (1 / J)'Last;    --@DIVISION_CHECK:FAIL
      Length : constant Integer := X (1 / J)'Length;  --@DIVISION_CHECK:FAIL
      --  Division-by-zero will fail

      First_Y  : constant Integer := Y.all (1)'First; --@DEREFERENCE_CHECK:FAIL
      Last_Y   : constant Integer := Y.all (1)'Last;  --@DEREFERENCE_CHECK:FAIL
      Length_Y : constant Integer := Y.all (1)'Length;--@DEREFERENCE_CHECK:FAIL
      --  Access dereference will fail
   begin
      null;
   end;
   Y : B := (others => (others => 123));
begin
   Test (Y, null, 0);
end;
