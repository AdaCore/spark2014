--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --clean BiasedDivide.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/BiasedDivide_types.txt
--    --output BiasedDivide.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

package BiasedDivide is

   procedure comp (y : Long_Float; z : Long_Float; r : out Long_Float)
   with
     Pre  => Z /= 4.0,
     Post => R = Y / (Z - 4.0);

end BiasedDivide;
--  @EOF
