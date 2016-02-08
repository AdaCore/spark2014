--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --clean ErrorExample.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/ErrorExample_types.txt
--    --output ErrorExample.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

package body ErrorExample is

   procedure comp
      (Requested_Force : Unsigned_32;
       Calculated_Force : Unsigned_32_m1_0_M100_0;
       Relative_Error : out Unsigned_32)
   is
      use type Unsigned_32;
      use type Unsigned_32_m1_0_M100_0;
      Abs_out1 : Unsigned_32;
   begin
      --  Block ErrorExample/Error Calc/Non-Zero
      --  Block ErrorExample/Requested\nForce
      --  Block ErrorExample/Error Calc/Division\nPre-Condition
      pragma Assert ((Requested_Force) /= (0), "Violation of assertion at block ErrorExample/Error Calc/Division\nPre-Condition");
      --  End Block ErrorExample/Error Calc/Division\nPre-Condition
      --  End Block ErrorExample/Requested\nForce
      --  End Block ErrorExample/Error Calc/Non-Zero

      --  Block ErrorExample/Error Calc/Error\nRatio
      --  Block ErrorExample/Requested\nForce
      --  Block ErrorExample/Calculated\nForce
      --  Block ErrorExample/Error Calc/Absolute\nError
      --  Block ErrorExample/Error Calc/Abs
      Abs_out1 := abs (((Requested_Force) - (Calculated_Force)) / (Requested_Force));
      --  End Block ErrorExample/Error Calc/Abs
      --  End Block ErrorExample/Error Calc/Absolute\nError
      --  End Block ErrorExample/Calculated\nForce
      --  End Block ErrorExample/Requested\nForce
      --  End Block ErrorExample/Error Calc/Error\nRatio

      --  Block ErrorExample/Less than\n1 percent
      --  Block ErrorExample/Consequent:\nAcceptable\nRelative Error\n
      pragma Assert ((Long_Float (Abs_out1)) <= (0.01), "Violation of assertion at block ErrorExample/Consequent:\nAcceptable\nRelative Error\n");
      --  End Block ErrorExample/Consequent:\nAcceptable\nRelative Error\n
      --  End Block ErrorExample/Less than\n1 percent

      --  Block ErrorExample/Relative\nError
      Relative_Error := Abs_out1;
      --  End Block ErrorExample/Relative\nError
   end comp;
end ErrorExample;
--  @EOF
