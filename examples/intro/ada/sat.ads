package Sat is

   subtype My_Int is Integer range 0 .. 10_000;

   function Add (X , Y : My_Int) return My_Int;
   --# return Sum => (X + Y < 10_000 and Sum = X + Y) or
   --#               (X + Y >= 10_000 and Sum = 10_000);

   function Mult (X , Y : My_Int) return My_Int;
   --# return Prod => (X * Y < 10_000 and Prod = X * Y) or
   --#                (X * Y >= 10_000 and Prod = 10_000);

end Sat;
