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

private package HW.GFX.GMA.Connectors.EDP
is

   procedure Pre_On (Pipe : Pipe_Index; Port_Cfg : Port_Config);

   procedure Post_On
     (Link     : in     DP_Link;
      Success  :    out Boolean);

   pragma Warnings (GNATprove, Off, "unused variable ""Port""",
                    Reason => "Needed for a common interface");
   procedure Off (Port : Digital_Port);
   pragma Warnings (GNATprove, On, "unused variable ""Port""");

   procedure Pre_Training;

end HW.GFX.GMA.Connectors.EDP;
