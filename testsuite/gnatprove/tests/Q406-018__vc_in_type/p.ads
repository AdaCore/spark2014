package P is

   type A is array (Boolean) of Integer;

   type T is private;

private

   type T is record
      C : A := (others => 0);  --  info: length check prove
   end record;

end;
