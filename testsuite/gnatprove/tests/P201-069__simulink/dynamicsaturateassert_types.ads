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

with Interfaces; use Interfaces;

package DynamicSaturateAssert_types is

   subtype Unsigned_32_m1_0_M100_0 is Unsigned_32 range Unsigned_32 (1.0) .. Unsigned_32 (100.0);

end DynamicSaturateAssert_types;
--  @EOF
