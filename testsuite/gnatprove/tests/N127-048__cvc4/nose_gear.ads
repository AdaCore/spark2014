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

with Interfaces; use Interfaces;

package nose_gear is

   procedure nose_gear_init;

   procedure nose_gear_initStates;

   procedure nose_gear_comp
      (NGRotations : Unsigned_16;
       NGClickTime : Unsigned_16;
       Millisecs : Unsigned_16;
       estimatedGroundVelocity : out Long_Float;
       estimatedGroundVelocityIsAvailable : out Boolean);

end nose_gear;
--  @EOF

