--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --no-misra
--    --clean ABS_Controller_oem_with_property.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/ABS_Controller_oem_with_property_types.txt
--    --output ABS_Controller_oem_with_property.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

package ABS_Controller_oem_with_property is

   procedure comp
      (Wheel_Speed : Long_Float;
       Vehicle_Speed : Long_Float;
       Apply_Brakes : out Long_Float)
   with
     Pre =>
       -- Violation of assertion at block ABS_Controller_oem_with_property/Applies Brake\nWhen At Rest\nAntecedent
       (Wheel_Speed) >= (2.2204e-16);

end ABS_Controller_oem_with_property;
--  @EOF
