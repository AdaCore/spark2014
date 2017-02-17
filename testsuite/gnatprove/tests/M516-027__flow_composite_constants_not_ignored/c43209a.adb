procedure c43209a is

   type Array_T is array (1 .. 3) of Integer;
   type Record_T is record
      A, B : Integer;
   end record;

   Y : constant Array_T := (others => 0);
   X : constant Record_T := (A => 12, B => 13);

begin

   if Y (2) /= X.A then
      null;
   end if;

end c43209a;
