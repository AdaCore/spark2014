with Ada.Numerics.Big_Numbers.Big_Reals; use Ada.Numerics.Big_Numbers.Big_Reals;
package Real_Convs is

   package My_Float_Conversions is new
     Float_Conversions (Num => Float);

   type My_Fixed is delta 3.0 / 2.0 ** 8 range -5.0 .. 5.0;

   package My_Fixed_Conversions is new
     Fixed_Conversions (Num => My_Fixed);
end Real_Convs;
