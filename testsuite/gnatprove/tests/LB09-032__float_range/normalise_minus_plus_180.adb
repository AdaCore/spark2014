--------------------------------------------------------------------------------
--                                                                            --
-- This document is the property of Astrium. It shall not be communicated to  --
-- third parties without prior written agreement.                             --
-- Its content shall not be disclosed.                                        --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- This software has been developed during a Research and Technology project  --
-- Its quality is not guaranteed                                              --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- The ATV Solar Generation System (SGS)
-- Company: Astrium Space Transportation
-- Author: David Lesens
--                                                                            --
--------------------------------------------------------------------------------

package body Normalise_Minus_Plus_180 is

   function Round_Toward_Minus_Infinite32 (X : in T_Float32 ) return T_Float32
   is
   begin
      return T_Float32'Floor (X);
   end Round_Toward_Minus_Infinite32;

   ----------------------------------------------------------------------
   -- INTERNAL SERVICE
   function S_NORMALISE_0_360(X : in T_FLOAT32) return T_Angle_360
   -- This service normalises the input angle X (degrees)
   -- in an angle having value in the RANGE 0 - 360
   -- This is performed returning an angle having value
   is
      Result : T_Float32;
   begin
      Result := X - (360.0 * Round_Toward_Minus_Infinite32(X / 360.0));
      pragma Assert(Result >= 0.0);
      pragma Assert(Result <= 360.0);
      return Result;
   end S_NORMALISE_0_360;

   ----------------------------------------------------------------------
   -- INTERNAL SERVICE
   function S_NORMALISE_MINUS_PLUS_180(X : in T_FLOAT32) return T_Angle_180
   -- This service normalises the input angle X (degrees)
   -- in an angle having value in the RANGE ]-180,180]
   -- This is performed returning an angle having value
   -- ANGLE := X - (C_PI_IN_DEGREES * FAS_MATH_LIB.S_GET_INT(X =>
   --    (X / C_PI_IN_DEGREES)))
   is
      NORM_X : T_FLOAT32;
   begin

      -- normalise in the RANGE [0,360[
      NORM_X := S_NORMALISE_0_360(X => X);
      pragma Assert(Norm_X >= 0.0);
      pragma Assert(Norm_X <= 360.0);

      -- if the normalised angle is > 180 then subtract 360.0
      if (NORM_X > 180.0) then
         pragma Assert(Norm_X > 180.0);
         pragma Assert(Norm_X <= 360.0);
         -- normalise the angle
         NORM_X := NORM_X - 360.0;
         pragma Assert(Norm_X >= -180.0);
         pragma Assert(Norm_X <= 180.0);
      else
         pragma Assert(Norm_X >= 0.0);
         pragma Assert(Norm_X <= 180.0);
      end if;

      -- return normalised angle to the caller
      return NORM_X;

   end S_NORMALISE_MINUS_PLUS_180;
   ----------------------------------------------------------------------

end Normalise_Minus_Plus_180;
