with Interfaces.C.Extensions; use Interfaces.C.Extensions;

--  Package wrapping functions from Power Management HAL

package PM_Pack
  with SPARK_Mode
is

   --  Procedures and functions

   function PM_Is_Discharging return bool
     with
       Global => null;
   pragma Import (C, PM_Is_Discharging, "pmIsDischarging");

end PM_Pack;
