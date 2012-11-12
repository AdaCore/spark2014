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

package Normalise_Minus_Plus_180 is

   type T_Float32 is digits 6  range -3.40282E+38 .. 3.40282E+38;
   subtype T_Angle_180 is T_Float32 range -180.0 .. 180.0;

   function S_NORMALISE_MINUS_PLUS_180(X : in T_FLOAT32) return T_Angle_180;

private

   subtype T_Angle_360 is T_Float32 range 0.0 .. 360.0;

   function Round_Toward_Minus_Infinite32 (X : in T_Float32) return T_Float32
   with
     Pre => ( X >= T_Float32'First + 1.0 ),
     Post => ( Round_Toward_Minus_Infinite32'Result <= X ) and then
     ( Round_Toward_Minus_Infinite32'Result >= X - 1.0 ) and then
     ( Round_Toward_Minus_Infinite32'Result = T_Float32'Floor (X) );

   function S_NORMALISE_0_360(X : in T_FLOAT32) return T_Angle_360;
--      with Post => (S_NORMALISE_0_360'Result >= 0.0) and then
--        (S_NORMALISE_0_360'Result <= 360.0);

end Normalise_Minus_Plus_180;
