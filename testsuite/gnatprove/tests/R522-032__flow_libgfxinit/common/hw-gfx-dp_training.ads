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

with HW.GFX.DP_Info;
with HW.GFX.DP_Aux_Ch;

private generic

   TPS3_Supported : Boolean;

   type T (<>) is limited private;
   type Aux_T (<>) is limited private;

   with package Aux_Ch is new DP_Aux_Ch (T => Aux_T, others => <>);

   with package DP_Info is new GFX.DP_Info (T => Aux_T, Aux_Ch => Aux_Ch);

   with function To_Aux (Port : T) return Aux_T;

   with function Max_V_Swing (Port : T) return DP_Info.DP_Voltage_Swing;

   with function Max_Pre_Emph
     (Port        : T;
      Train_Set   : DP_Info.Train_Set)
      return DP_Info.DP_Pre_Emph;

   with procedure Set_Pattern
     (Port        : T;
      Link        : DP_Link;
      Pattern     : DP_Info.Training_Pattern);

   with procedure Set_Signal_Levels
     (Port        : T;
      Link        : DP_Link;
      Train_Set   : DP_Info.Train_Set);

   with procedure Off (Connector : T);

package HW.GFX.DP_Training
is

   procedure Train_DP
     (Port     : in     T;
      Link     : in     DP_Link;
      Success  :    out Boolean);

end HW.GFX.DP_Training;
