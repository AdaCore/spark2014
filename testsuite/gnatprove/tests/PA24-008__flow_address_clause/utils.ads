with Interfaces;

package Utils
with
   SPARK_Mode
is

   function Read_Register
     (Address : Interfaces.Unsigned_64)
      return Interfaces.Unsigned_64;

end Utils;
