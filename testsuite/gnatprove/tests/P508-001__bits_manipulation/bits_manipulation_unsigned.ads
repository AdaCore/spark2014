with Code_Config;
with Interfaces;
with Bits_Manipulation.Functions;
pragma Elaborate_All (Bits_Manipulation.Functions);

package Bits_Manipulation_Unsigned
with SPARK_Mode is

   package Code_Parameters is new
        Code_Config.Parameters (Proved       => True,
                                Optimize_For => Code_Config.Fast_And_Large,
                                Inline       => Code_Config.Inline_Always,
                                Safe         => Code_Config.Default);

   generic
      type Modular is mod <>;
   package Unsigned_Generic is

      package BM is new Bits_Manipulation (Modular, Code_Parameters => Code_Parameters);
      package Functions is new BM.Functions;

      subtype Bit_Position is BM.Bit_Position;
      subtype Mask_Size is BM.Mask_Size;

      function Extract_Bits (V : Modular; From, To : Bit_Position) return Modular
                             renames Functions.Extract_Bits;

      function Shift_Right (V : Modular; Amount : Natural) return Modular
                            renames Functions.Shift_Right;

      function Shift_Left (V : Modular; Amount : Natural) return Modular
                           renames Functions.Shift_Left;

      function Make_Mask (Num_Bits : Mask_Size) return Modular
                          renames Functions.Make_Mask;

      function MSB_Index (Value : Modular) return Bit_Position
                          renames Functions.MSB_Index;

   end Unsigned_Generic;

   package Unsigned_8 is new Unsigned_Generic (Interfaces.Unsigned_8);
   package Unsigned_16 is new Unsigned_Generic (Interfaces.Unsigned_16);
   package Unsigned_32 is new Unsigned_Generic (Interfaces.Unsigned_32);
   package Unsigned_64 is new Unsigned_Generic (Interfaces.Unsigned_64);

end Bits_Manipulation_Unsigned;
