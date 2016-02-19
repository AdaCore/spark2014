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

with AssertionProperties_types; use AssertionProperties_types;

package AssertionProperties is

   procedure comp (x : Long_Float_m0_0_MInf; y : out Long_Float)
   with
     -- Violation of assertion at block AssertionProperties/Antecedent
     Pre => (x) /= (16.0);

end AssertionProperties;
--  @EOF
