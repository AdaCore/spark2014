--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --clean AssertionProperties.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/AssertionProperties_types.txt
--    --output AssertionProperties.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

with Simulink_Functions; use Simulink_Functions;

package body AssertionProperties is

   procedure comp (x : Long_Float_m0_0_MInf; y : out Long_Float) is
      use type Long_Float;
      use type Long_Float_m0_0_MInf;
      Sqrt_out1 : Long_Float;
   begin
      --  Block AssertionProperties/x
      --  Block AssertionProperties/Sqrt
      Sqrt_out1 := pow (x, Long_Float (0.5));
      --  End Block AssertionProperties/Sqrt
      --  End Block AssertionProperties/x

      --  Block AssertionProperties/y
      y := Sqrt_out1;
      --  End Block AssertionProperties/y

      --  Block AssertionProperties/Not Equal\nTo 16
      --  Block AssertionProperties/x
      --  Block AssertionProperties/Antecedent
      pragma Assert ((x) /= (16.0), "Violation of assertion at block AssertionProperties/Antecedent");
      --  End Block AssertionProperties/Antecedent
      --  End Block AssertionProperties/x
      --  End Block AssertionProperties/Not Equal\nTo 16

      --  Block AssertionProperties/Not Equal\nTo 4
      --  Block AssertionProperties/Consequent
      pragma Assert ((Sqrt_out1) /= (4.0), "Violation of assertion at block AssertionProperties/Consequent");
      --  End Block AssertionProperties/Consequent
      --  End Block AssertionProperties/Not Equal\nTo 4
   end comp;
end AssertionProperties;
--  @EOF
