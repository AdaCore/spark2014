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

with HW.GFX.DP_Aux_Ch;

private generic

   type T (<>) is limited private;

   with package Aux_Ch is new DP_Aux_Ch (T => T, others => <>);

package HW.GFX.DP_Info is

   type DP_Voltage_Swing is (VS_Level_0, VS_Level_1, VS_Level_2, VS_Level_3);

   type DP_Pre_Emph is (Emph_Level_0, Emph_Level_1, Emph_Level_2, Emph_Level_3);

   type Train_Set is record
      Voltage_Swing  : DP_Voltage_Swing;
      Pre_Emph       : DP_Pre_Emph;
   end record;

   type Training_Pattern is (TP_1, TP_2, TP_3, TP_Idle, TP_None);

   ----------------------------------------------------------------------------

   type Lane_Index is new Natural range 0 .. 3;

   type Lane_Status is record
      CR_Done           : Boolean;
      Channel_EQ_Done   : Boolean;
      Symbol_Locked     : Boolean;
      Reserved          : Boolean;
   end record;
   for Lane_Status use record
      CR_Done           at 16#00# range 0 .. 0;
      Channel_EQ_Done   at 16#00# range 1 .. 1;
      Symbol_Locked     at 16#00# range 2 .. 2;
      Reserved          at 16#00# range 3 .. 3;
   end record;
   type Lanes_Status is array (Lane_Index) of Lane_Status;
   pragma Pack (Lanes_Status);

   type Adjust_Request is record
      Voltage_Swing  : DP_Voltage_Swing;
      Pre_Emph       : DP_Pre_Emph;
   end record;
   for Adjust_Request use record
      Voltage_Swing  at 16#00# range 0 .. 1;
      Pre_Emph       at 16#00# range 2 .. 3;
   end record;
   type Adjust_Requests_Array is array (Lane_Index) of Adjust_Request;
   pragma Pack (Adjust_Requests_Array);

   type Link_Status is record
      Lanes                : Lanes_Status;
      Interlane_Align_Done : Boolean;
      Adjust_Requests      : Adjust_Requests_Array;
   end record;
   for Link_Status use record
      Lanes                at 16#00# range 0 .. 15;
      Interlane_Align_Done at 16#02# range 0 ..  0;
      Adjust_Requests      at 16#04# range 0 .. 15;
   end record;

   ----------------------------------------------------------------------------

   procedure Read_Caps
     (Link     : in out DP_Link;
      Port     : in     T;
      Success  :    out Boolean);

   procedure Preferred_Link_Setting
     (Link        : in out DP_Link;
      Mode        : in     Mode_Type;
      Success     :    out Boolean);

   procedure Next_Link_Setting
     (Link        : in out DP_Link;
      Mode        : in     Mode_Type;
      Success     :    out Boolean);

   pragma Warnings
     (GNATprove, Off, "subprogram ""Dump_Link_Setting"" has no effect",
      Reason => "It's only used for debugging");
   procedure Dump_Link_Setting (Link : DP_Link);

   ----------------------------------------------------------------------------

   M_N_Max : constant := 2 ** 24 - 1;

   subtype M_Type is Int64 range 0 .. M_N_Max;
   subtype N_Type is Int64 range 0 .. M_N_Max;

   procedure Calculate_M_N
     (Link     : in     DP_Link;
      Mode     : in     Mode_Type;
      Data_M   :    out M_Type;
      Data_N   :    out N_Type;
      Link_M   :    out M_Type;
      Link_N   :    out N_Type);

   ----------------------------------------------------------------------------

   procedure Read_Link_Status
     (Port     : in     T;
      Status   :    out Link_Status;
      Success  :    out Boolean);

   function All_CR_Done
     (Status   : Link_Status;
      Link     : DP_Link)
      return Boolean;

   function All_EQ_Done
     (Status   : Link_Status;
      Link     : DP_Link)
      return Boolean;

   function Max_Requested_VS
     (Status   : Link_Status;
      Link     : DP_Link)
      return DP_Voltage_Swing;

   function Max_Requested_Emph
     (Status   : Link_Status;
      Link     : DP_Link)
      return DP_Pre_Emph;

end HW.GFX.DP_Info;
