with Interfaces; use Interfaces;
package P with SPARK_Mode is
   type Buffer_Type is array (Natural range <>) of Interfaces.Unsigned_8
     with Volatile;

   procedure Do_Something
     (Buf : in out Buffer_Type;
      I   : in     Natural)
     with
     Pre => I < Buf'Length;

end P;
