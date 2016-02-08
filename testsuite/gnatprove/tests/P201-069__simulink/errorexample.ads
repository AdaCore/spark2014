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

with ErrorExample_types; use ErrorExample_types;
with Interfaces; use Interfaces;

package ErrorExample is

   procedure comp
      (Requested_Force : Unsigned_32;
       Calculated_Force : Unsigned_32_m1_0_M100_0;
       Relative_Error : out Unsigned_32)
   with
     -- Violation of assertion at block ErrorExample/Error Calc/Division\nPre-Condition
     Pre  => (Requested_Force) /= (0),
     Post => Relative_Error = abs (((Requested_Force) - (Calculated_Force)) / (Requested_Force));
end ErrorExample;
--  @EOF
