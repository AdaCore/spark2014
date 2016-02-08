--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --clean DynamicSaturateAssert.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/DynamicSaturateAssert_types.txt
--    --output DynamicSaturateAssert.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

with DynamicSaturateAssert_types; use DynamicSaturateAssert_types;
with Interfaces; use Interfaces;

package DynamicSaturateAssert is

   procedure comp
      (Value : Unsigned_32_m1_0_M100_0;
       Max : Unsigned_32_m1_0_M100_0;
       Min : Unsigned_32_m1_0_M100_0;
       Saturated_Value : out Unsigned_32)
   with
     -- Violation of assertion at block DynamicSaturateAssert/In Between\nPre-Condition
     Pre => (Max) >= (Min);

end DynamicSaturateAssert;
--  @EOF
