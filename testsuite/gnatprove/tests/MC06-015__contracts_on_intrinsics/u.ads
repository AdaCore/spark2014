package U
  with SPARK_Mode => On
is

   type U32 is mod 2**32;

   function Shift_Right (Value  : U32;
                         Amount : Natural) return U32
     with Global => null,
          Import,
          Convention => Intrinsic,
          Pre  => Amount <= 16,
          Post => Shift_Right'Result = (Value / (2 ** Amount));

end U;
