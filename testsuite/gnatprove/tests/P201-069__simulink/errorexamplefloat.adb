--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0 (20151104)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --clean ErrorExampleFloat.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/ErrorExampleFloat_types.txt
--    --output ErrorExampleFloat.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

package body ErrorExampleFloat is

   procedure comp
      (Requested_Force : Long_Float_M2_220446049250313e_16_MInf;
       Calculated_Force : Long_Float_m1_0_M100_0;
       Relative_Error : out Long_Float)
   is
      use type Long_Float;
      use type Long_Float_m1_0_M100_0;
      use type Long_Float_M2_220446049250313e_16_MInf;
      Abs_out1 : Long_Float;
   begin
      --  Block ErrorExampleFloat/Error Calc/Non-Zero
      --  Block ErrorExampleFloat/Requested\nForce
      --  Block ErrorExampleFloat/Error Calc/Division\nPre-Condition
      pragma Assert ((Requested_Force) /= (0.0), "Violation of assertion at block ErrorExampleFloat/Error Calc/Division\nPre-Condition");
      --  End Block ErrorExampleFloat/Error Calc/Division\nPre-Condition
      --  End Block ErrorExampleFloat/Requested\nForce
      --  End Block ErrorExampleFloat/Error Calc/Non-Zero

      --  Block ErrorExampleFloat/Error Calc/Error\nRatio
      --  Block ErrorExampleFloat/Requested\nForce
      --  Block ErrorExampleFloat/Calculated\nForce
      --  Block ErrorExampleFloat/Error Calc/Absolute\nError
      --  Block ErrorExampleFloat/Error Calc/Abs
      Abs_out1 := abs (((Requested_Force) - (Calculated_Force)) / (Requested_Force));
      --  End Block ErrorExampleFloat/Error Calc/Abs
      --  End Block ErrorExampleFloat/Error Calc/Absolute\nError
      --  End Block ErrorExampleFloat/Calculated\nForce
      --  End Block ErrorExampleFloat/Requested\nForce
      --  End Block ErrorExampleFloat/Error Calc/Error\nRatio

      --  Block ErrorExampleFloat/Less than\n1 percent
      --  Block ErrorExampleFloat/Consequent:\nAcceptable\nRelative Error\n
      pragma Assert ((Abs_out1) <= (0.01), "Violation of assertion at block ErrorExampleFloat/Consequent:\nAcceptable\nRelative Error\n");
      --  End Block ErrorExampleFloat/Consequent:\nAcceptable\nRelative Error\n
      --  End Block ErrorExampleFloat/Less than\n1 percent

      --  Block ErrorExampleFloat/Relative\nError
      Relative_Error := Abs_out1;
      --  End Block ErrorExampleFloat/Relative\nError
   end comp;
end ErrorExampleFloat;
--  @EOF
