procedure W is
   type A is array (1 .. 1) of Integer;
   type B is array (1 .. 1) of A;
   procedure Test (X : B; Y : access constant B; J : Integer) with Pre => True is
      First  : constant Integer := X (1 / J)'First;
      Last   : constant Integer := X (1 / J)'Last;
      Length : constant Integer := X (1 / J)'Length;
      --  Division-by-zero will fail

      First_Y  : constant Integer := Y.all (1)'First;
      Last_Y   : constant Integer := Y.all (1)'Last;
      Length_Y : constant Integer := Y.all (1)'Length;
      --  Access dereference will fail
   begin
      null;
   end;
   Y : B := (others => (others => 123));
begin
   Test (Y, null, 0);
end;
