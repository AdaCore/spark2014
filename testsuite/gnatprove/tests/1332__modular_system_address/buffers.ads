with System;
with Types;

package Buffers
with
  SPARK_Mode,
  Abstract_State => State,
  Initializes    => State
is

   function Map_Address (Buffer : Types.Buffer_Range) return Types.Buffer_Address_Type;

end Buffers;
