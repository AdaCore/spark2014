package Sat
  with SPARK_Mode
is

   ------------------------------------------------------
   -- A simple abstract data type (ADT) for saturating --
   -- mathematics on integers.                         --
   --                                                  --
   -- Illustrates use of Contract_Cases in SPARK 2014  --
   ------------------------------------------------------

   subtype My_Int is Integer range 0 .. 10_000;

   function Add (X, Y : My_Int) return My_Int with
     Contract_Cases => (X + Y < 10_000  => Add'Result = X + Y,
                        X + Y >= 10_000 => Add'Result = 10_000);

   function Mult (X, Y : My_Int) return My_Int with
     Contract_Cases => (X * Y < 10_000  => Mult'Result = X * Y,
                        X * Y >= 10_000 => Mult'Result = 10_000);

end Sat;
