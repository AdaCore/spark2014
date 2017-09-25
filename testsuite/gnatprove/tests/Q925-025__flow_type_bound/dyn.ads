package Dyn with SPARK_Mode is
   X : Integer := 10;
   type T is array (Integer range <>) of Integer;
   type R is record
      Y : T(1 .. X);
   end record;
end Dyn;
