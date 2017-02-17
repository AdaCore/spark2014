with Ada.Unchecked_Conversion;

package body prover_crash
   with SPARK_Mode => On
is

   function Crash
     (X, Y : Myint) return Myfloat
   is
       function Conv is
        new Ada.Unchecked_Conversion (Myint, Myfloat);

   begin
      return (Conv (X + Y));
   end Crash;

end prover_crash;
