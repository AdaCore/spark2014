--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator (dev)
--  Command line arguments: -l ada
--    --pre-process-xmi
--    --clean finnuc.xmi

pragma Style_Checks ("M999");  --  ignore long lines

package finnuc_types is

   subtype Boolean_Array_3_Range_1 is Integer range 1 .. 3;
   type Boolean_Array_3 is array (Boolean_Array_3_Range_1) of Boolean;
   subtype Boolean_Array_8_2_Range_1 is Integer range 1 .. 8;
   subtype Boolean_Array_8_2_Range_2 is Integer range 1 .. 2;
   type Boolean_Array_8_2 is array (Boolean_Array_8_2_Range_1, Boolean_Array_8_2_Range_2) of Boolean;
end finnuc_types;
--  @EOF
