--
-- Copyright (C) 2015-2016 secunet Security Networks AG
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

private package HW.GFX.GMA.Connectors is

   pragma Warnings (GNATprove, Off, "subprogram ""*"" has no effect",
                    Reason => "Only effects some platforms");
   procedure Post_Reset_Off;
   procedure Initialize;
   pragma Warnings (GNATprove, On, "subprogram ""*"" has no effect");

   pragma Warnings (GNATprove, Off, "unused variable ""P*""",
                    Reason => "Needed for a common interface");
   procedure Pre_On
     (Pipe        : in     Pipe_Index;
      Port_Cfg    : in     Port_Config;
      PLL_Hint    : in     Word32;
      Success     :    out Boolean);

   procedure Post_On
     (Pipe     : in     Pipe_Index;
      Port_Cfg : in     Port_Config;
      PLL_Hint : in     Word32;
      Success  :    out Boolean);
   pragma Warnings (GNATprove, On, "unused variable ""P*""");

   procedure Pre_Off (Port_Cfg : Port_Config);
   procedure Post_Off (Port_Cfg : Port_Config);

   procedure Pre_All_Off;
   procedure Post_All_Off;

end HW.GFX.GMA.Connectors;
