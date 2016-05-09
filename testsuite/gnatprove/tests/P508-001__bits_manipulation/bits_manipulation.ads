with Code_Config;
generic
   type Modular is mod <>;
   Modular_Size : Positive := Modular'Size;
   with package Code_Parameters is new Code_Config.Parameters (<>);
package Bits_Manipulation with SPARK_Mode is

   Pragma Pure;

   subtype Bit_Position is Natural range 0 .. Modular_Size - 1;
   subtype Mask_Size is Natural range 1 .. Modular_Size;

end Bits_Manipulation;
