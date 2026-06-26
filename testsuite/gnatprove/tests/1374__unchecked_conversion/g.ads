with SPARK.Conversions.Access_Conversions;
with Interfaces; use Interfaces;
generic
   type Element_Type is private;
   --  Any type that fits in a 32-bit cell.

package G with
    SPARK_Mode
is
   pragma
     Compile_Time_Error
       (Element_Type'Object_Size > 32,
        "Element_Type must fit in 32 bits");

   type Bit is mod 2 with Size => 1;
   type Padding_Type is array (Positive range <>) of Bit with Pack;

   type Padded is record
      Value : aliased Element_Type;
      Pad   : Padding_Type (1 .. 32 - Element_Type'Object_Size);
   end record
   with Alignment => 4;

   package Conv is new
     SPARK.Conversions.Access_Conversions.Access_Variable_Conversions
       (Source_Type => Unsigned_32, Target_Type => Padded);

end G;
