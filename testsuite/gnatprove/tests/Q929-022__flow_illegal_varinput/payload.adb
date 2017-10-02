with Byte_Types;

package body Payload
  with SPARK_Mode => On
is

   function Get_Packed_Payload (Data : T) return Byte_Types.Byte_Array
   is
   begin

      return Data.Payload;

   end Get_Packed_Payload;


end Payload;
