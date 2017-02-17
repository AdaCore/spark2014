--  Copyright (C) Project P consortium
--
--  @generated with GNAT Model Compiler 1.0w
--  Command line arguments:
--
--    --clean nose_gear.mdl
--    --typing nose_gear_types.txt
--    --matlab nose_gear_def.m
--    --language ada

pragma Style_Checks ("M999");  --  ignore long lines

package nose_gear_params is
   PI : constant Long_Float := 3.14;
   WHEEL_DIAMETER : constant Long_Float := 0.0005588;
   VALIDITY_PERIOD : constant Long_Float := 3.0E+03;
   UPDATE_PERIOD : constant Long_Float := 5.0E+02;

end nose_gear_params;
--  @EOF

