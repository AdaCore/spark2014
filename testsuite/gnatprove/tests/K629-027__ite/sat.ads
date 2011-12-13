package Sat is

   subtype My_Int is Integer range 0 .. 10_000;

   function Add (X , Y : My_Int) return My_Int with
     Post => (X + Y < 10_000 and Add'Result = X + Y) or
             (X + Y >= 10_000 and Add'Result = 10_000);

end Sat;
