--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --no-misra
--    --clean ABS_Controller_supplier_with_property.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/ABS_Controller_supplier_with_property_types.txt
--    --output ABS_Controller_supplier_with_property.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

with Interfaces; use Interfaces;

package ABS_Controller_supplier_with_property is

   procedure comp
      (Wheel_Speed : Unsigned_32;
       Vehicle_Speed : Unsigned_32;
       Apply_Brakes : out Integer_32);

end ABS_Controller_supplier_with_property;
--  @EOF
