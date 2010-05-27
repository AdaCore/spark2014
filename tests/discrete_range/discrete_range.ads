package Discrete_Range is

   type Arr is array (Positive range <>) of Integer;

   X1 : Arr (Positive'Range);

   X2 : Arr (Positive'First .. 10);

   X3 : Arr (1 .. Positive'Last);

   X4 : Arr (1 .. 10);

   procedure Init;
   --# global out X1, X2, X3, X4;

end;
