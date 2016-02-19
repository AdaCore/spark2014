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

package ErrorExampleFloat_types is

   subtype Long_Float_m1_0_M100_0 is Long_Float range 1.0 .. 100.0;

   subtype Long_Float_M2_220446049250313e_16_MInf is Long_Float range 2.220446049250313e-16 .. Long_Float'Last;

end ErrorExampleFloat_types;
--  @EOF
