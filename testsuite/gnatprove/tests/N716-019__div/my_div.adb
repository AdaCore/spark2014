package body My_Div
is

   procedure P (X : in out My_Int) is
   begin
      X := X / 4;
      X := X / 4;
      X := X / 4;
   end P;

   procedure Q (X : in out My_Int) is
   begin
      X := X / (-1);
   end Q;

end My_Div;
