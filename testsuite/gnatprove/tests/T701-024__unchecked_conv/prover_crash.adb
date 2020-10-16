with Ada.Unchecked_Conversion;

package body prover_crash with
   SPARK_Mode => On
is

   function Crash (X, Y : Myint) return Boolean is
      function Conv is new Ada.Unchecked_Conversion (Myint, Myfloat);

   begin
      return Conv (S => X + Y) = Conv (X + Y);
      --  Identical calls with and without named parameter association
   end Crash;

end prover_crash;
