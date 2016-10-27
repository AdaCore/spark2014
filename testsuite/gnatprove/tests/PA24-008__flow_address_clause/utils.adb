with System;

package body Utils
with
   SPARK_Mode
is

   function Read_Register
     (Address : Interfaces.Unsigned_64)
      return Interfaces.Unsigned_64
   is
      Reg : Interfaces.Unsigned_64
      with
         Import,
         Address => System'To_Address (Address);
   begin
      return Reg;
   end Read_Register;

end Utils;
