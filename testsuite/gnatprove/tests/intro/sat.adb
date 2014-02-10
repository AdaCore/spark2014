package body Sat
  with SPARK_Mode
is

   ------------------------------------------------------
   -- Sat package - body                               --
   --                                                  --
   -- Illustrates use of conditional expressions and   --
   -- bodies completed by an expression function.      --
   ------------------------------------------------------

   function Add (X, Y : My_Int) return My_Int is
     (if X + Y < 10_000 then
         X + Y
       else
         10_000);

   function Mult (X, Y : My_Int) return My_Int is
     (if X * Y < 10_000 then
         X * Y
       else
         10_000);

end Sat;
