--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --clean Smoothing.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/Smoothing_types.txt
--    --output Smoothing.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

package Smoothing is

   procedure comp
      (New_Value : Long_Float;
       Prior_Value : Long_Float;
       Smoothing_Factor : Long_Float;
       Smoothed_Value : out Long_Float)
   with
     Pre =>
       -- Violation of assertion at block Smoothing/Antecedent:\nFactor Greater\nThan One
       (Smoothing_Factor) > (1.0)

       -- Restrict to non-negative values, which would require more complex treatment of subtraction
       and then New_Value >= 0.0
       and then Prior_Value >= 0.0;
end Smoothing;
--  @EOF
