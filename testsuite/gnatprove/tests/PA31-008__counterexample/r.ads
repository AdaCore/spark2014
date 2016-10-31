with Interfaces;
use type Interfaces.Unsigned_8;

package R
 with SPARK_Mode => On
is
   subtype Byte  is Interfaces.Unsigned_8;
   subtype Index is Positive range 1 .. 2500;
   type Byte_Seq is array (Index) of Byte;

   subtype Seq_Bit_Count is Natural range 0 .. Byte_Seq'Length * 8;

   function Ones_Count (D : in Byte_Seq) return Seq_Bit_Count;

end R;
