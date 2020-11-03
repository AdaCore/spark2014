pragma SPARK_Mode;

package Test_Fixed_Points is

   pragma Warnings
     (Off, "postcondition does not check the outcome of calling");

   Small : constant := 2.0 ** (-31);
   type Fix is delta Small range -1.0 .. 1.0 - Small;

   procedure Test_Div_Is_Monotonic
     (Val1  : Fix;
      Val2  : Fix;
      Denom : Positive)
   with
     Global => null,
     Pre  => Val1 <= Val2,
     Post => Val1 / Denom <= Val2 / Denom;

   procedure Test_Div_Right_Is_Monotonic
     (Num    : Fix;
      Denom1 : Positive;
      Denom2 : Positive)
   with
     Global => null,
     Pre  => Num >= 0.0
       and then Denom1 <= Denom2,
     Post => Num / Denom1 >= Num / Denom2;

   procedure Test_Mult_Then_Div_Is_Ident
     (Val1 : Fix;
      Val2 : Positive)
   with
     Global => null,
     Pre  => Val1 in 0.0 .. Fix'Last / Val2 - Fix'Small,
     Post => (Val1 * Val2) / Val2 = Val1;

end Test_Fixed_Points;
