pragma SPARK_Mode;
with Types; use Types;

package Repr with
  SPARK_Mode
is

   procedure Initialize (Buffer : out Bytes_Ptr);

end Repr;
