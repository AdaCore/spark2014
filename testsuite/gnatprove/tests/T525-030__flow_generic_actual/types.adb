with Ada.Numerics.Big_Numbers.Big_Integers;

package body Types is

   function Extract_Mod return Value is
      package Conversions is new Ada.Numerics.Big_Numbers.Big_Integers.Unsigned_Conversions (Value);
   begin
      return Value'First;
   end Extract_Mod;

end Types;
