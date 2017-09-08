package body Test
  with SPARK_Mode => On
is


   function Serialize return Byte_Array
   is
      Constrained_Array : Byte_Array (1 .. 500) := (others => 0);
   begin
      return Constrained_Array;
   end Serialize;

end Test;
