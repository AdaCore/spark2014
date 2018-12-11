--
-- Copyright (C) 2015-2017 secunet Security Networks AG
--
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--

with HW;

private package HW.GFX.GMA.Config_Helpers
is

   function To_GPU_Port
     (Pipe  : Pipe_Index;
      Port  : Active_Port_Type)
      return GPU_Port;

   function To_PCH_Port (Port : Active_Port_Type) return PCH_Port;

   function To_Display_Type (Port : Active_Port_Type) return Display_Type;

   procedure Fill_Port_Config
     (Port_Cfg :    out Port_Config;
      Pipe     : in     Pipe_Index;
      Port     : in     Port_Type;
      Mode     : in     Mode_Type;
      Success  :    out Boolean);

   ----------------------------------------------------------------------------

   pragma Warnings (GNAT, Off, """Integer_32"" is already use-visible *",
                    Reason => "Needed for older compiler versions");
   use type HW.Pos32;
   pragma Warnings (GNAT, On, """Integer_32"" is already use-visible *");
   function Validate_Config
     (FB                : Framebuffer_Type;
      Mode              : Mode_Type;
      Pipe              : Pipe_Index;
      Scaler_Available  : Boolean)
      return Boolean
   with
      Post =>
        (if Validate_Config'Result then
            Rotated_Width (FB) <= Mode.H_Visible and
            Rotated_Height (FB) <= Mode.V_Visible and
            (FB.Offset = VGA_PLANE_FRAMEBUFFER_OFFSET or
             FB.Height + FB.Start_Y <= FB.V_Stride));

end HW.GFX.GMA.Config_Helpers;
