package Widths with SPARK_Mode is
   type Octet is mod 256;
   type Pair is record
      Left, Right : Octet;
   end record;
   type Four is array (1 .. 4) of Pair;

   procedure Check;
end Widths;
