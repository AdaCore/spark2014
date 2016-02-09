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

with ErrorExampleFloat_types; use ErrorExampleFloat_types;

package ErrorExampleFloat is

   procedure comp
      (Requested_Force : Long_Float_M2_220446049250313e_16_MInf;
       Calculated_Force : Long_Float_m1_0_M100_0;
       Relative_Error : out Long_Float)
   with
     -- Violation of assertion at block ErrorExampleFloat/Error Calc/Division\nPre-Condition
     Pre => (Requested_Force) /= (0.0);

end ErrorExampleFloat;
--  @EOF
