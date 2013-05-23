package body Body_Contract is

   procedure P1 (X : in out Integer) is
      pragma Precondition (X > 0);
      pragma Postcondition (X = X'Old - 1);
   begin
      X := X - 1;
   end P1;

   procedure P2 (X : in out Integer) with
     Pre  => X > 0,
     Post => X = X'Old - 1
   is
   begin
      X := X - 1;
   end P2;

   procedure P3 (X : in out Integer) is
      pragma Precondition (X > -1);
      pragma Postcondition (X < X'Old);
   begin
      X := X - 1;
   end P3;

end Body_Contract;
