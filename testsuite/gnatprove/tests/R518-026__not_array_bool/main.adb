procedure Main is
   type A is array (Integer range 1 .. 10) of Boolean;

   X : A := (others => True);
   Y : A := not X;

begin
   pragma Assert (not Y (1));
end;
