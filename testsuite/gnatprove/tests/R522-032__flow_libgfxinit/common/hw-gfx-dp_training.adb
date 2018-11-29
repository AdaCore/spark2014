--
-- Copyright (C) 2015-2016 secunet Security Networks AG
-- Copyright (C) 2017 Nico Huber <nico.h@gmx.de>
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

with Ada.Unchecked_Conversion;

with HW.Debug;
with GNAT.Source_Info;

with HW.Time;
with HW.GFX.DP_Defs;

package body HW.GFX.DP_Training is

   pragma Warnings (GNATprove, Off, "unused initial value of ""Port""*",
                    Reason => "Needed for a common interface");
   function Training_Set
     (Port        : T;
      Train_Set   : DP_Info.Train_Set)
      return Word8
   is
      use type DP_Info.DP_Voltage_Swing;
      use type DP_Info.DP_Pre_Emph;
      use type Word8;
      Value : Word8;
   begin
      case Train_Set.Voltage_Swing is
         when DP_Info.VS_Level_0   => Value := 16#00#;
         when DP_Info.VS_Level_1   => Value := 16#01#;
         when DP_Info.VS_Level_2   => Value := 16#02#;
         when DP_Info.VS_Level_3   => Value := 16#03#;
      end case;
      if Train_Set.Voltage_Swing = Max_V_Swing (Port) then
         Value := Value or 16#04#;
      end if;

      case Train_Set.Pre_Emph is
         when DP_Info.Emph_Level_0 => Value := Value or 16#00#;
         when DP_Info.Emph_Level_1 => Value := Value or 16#08#;
         when DP_Info.Emph_Level_2 => Value := Value or 16#10#;
         when DP_Info.Emph_Level_3 => Value := Value or 16#18#;
      end case;
      if Train_Set.Pre_Emph = Max_Pre_Emph (Port, Train_Set) then
         Value := Value or 16#20#;
      end if;

      return Value;
   end Training_Set;
   pragma Warnings (GNATprove, On, "unused initial value of ""Port""*");

   ----------------------------------------------------------------------------

   function Lane_Count (Link : DP_Link) return Positive
   with
      Post => Lane_Count'Result <= 4
   is
   begin
      return Positive (Lane_Count_As_Integer (Link.Lane_Count));
   end Lane_Count;

   procedure Sink_Init
     (Port        : in     Aux_T;
      Link        : in     DP_Link;
      Success     :    out Boolean)
   is
      use type Word8;
      function Link_Rate_As_Word8 is new Ada.Unchecked_Conversion
        (Source => DP_Bandwidth, Target => Word8);
      Data : DP_Defs.Aux_Payload;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Data :=
        (0      => Link_Rate_As_Word8 (Link.Bandwidth),
         1      => Word8 (Lane_Count (Link)),
         others => 0);  -- Don't care

      if Link.Enhanced_Framing then
         Data (1) := Data (1) or 16#80#;
      end if;

      Aux_Ch.Aux_Write
        (Port     => Port,
         Address  => 16#00100#,     -- LINK_BW_SET, LANE_COUNT_SET
         Length   => 2,
         Data     => Data,
         Success  => Success);
      Success := Success or Link.Opportunistic_Training;

      if Success then
         Data (0) := 16#00#;  -- no downspread
         Data (1) := 16#01#;  -- ANSI8B10B coding

         Aux_Ch.Aux_Write
           (Port     => Port,
            Address  => 16#00107#,     -- DOWNSPREAD_CTRL,
            Length   => 2,             -- MAIN_LINK_CHANNEL_CODING_SET
            Data     => Data,
            Success  => Success);
         Success := Success or Link.Opportunistic_Training;
      end if;
   end Sink_Init;

   procedure Sink_Set_Training_Pattern
     (DP          : in     Aux_T;
      Link        : in     DP_Link;
      Pattern     : in     DP_Info.Training_Pattern;
      Success     :    out Boolean)
   is
      use type DP_Info.Training_Pattern;

      type TP_Array is array (DP_Info.Training_Pattern) of Word8;
      TP : constant TP_Array := TP_Array'
        (DP_Info.TP_1 => 16#21#, DP_Info.TP_2 => 16#22#, DP_Info.TP_3 => 16#23#,
         DP_Info.TP_Idle => 16#00#, DP_Info.TP_None => 16#00#);

      Data : DP_Defs.Aux_Payload;
      Length : Positive := 1;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Data :=
        (0      => TP (Pattern),
         others => 0);  -- Don't care

      if Pattern < DP_Info.TP_Idle then
         Length := Length + Lane_Count (Link);
      end if;
      Aux_Ch.Aux_Write
        (Port     => DP,
         Address  => 16#00102#,     -- TRAINING_PATTERN_SET
         Length   => Length,
         Data     => Data,
         Success  => Success);
   end Sink_Set_Training_Pattern;

   procedure Sink_Set_Signal_Levels
     (Port        : in     T;
      DP          : in     Aux_T;
      Link        : in     DP_Link;
      Train_Set   : in     DP_Info.Train_Set;
      Success     :    out Boolean)
   is
      Data  : DP_Defs.Aux_Payload;
      T_Set : constant Word8 := Training_Set (Port, Train_Set);
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Data                                := (others => 0); -- Initialize
      Data (0 .. Lane_Count (Link) - 1)   := (others => T_Set);

      Aux_Ch.Aux_Write
        (Port     => DP,
         Address  => 16#00103#,     -- TRAINING_LANEx_SET
         Length   => Lane_Count (Link),
         Data     => Data,
         Success  => Success);
   end Sink_Set_Signal_Levels;

   pragma Warnings (GNATprove, Off, "unused initial value of ""Port""*",
                    Reason => "Needed for a common interface");
   procedure Sink_Adjust_Training
     (Port        : in     T;
      DP          : in     Aux_T;
      Link        : in     DP_Link;
      Train_Set   : in out DP_Info.Train_Set;
      CR_Done     : in out Boolean;
      EQ_Done     :    out Boolean;
      Success     :    out Boolean)
   is
      use type DP_Info.DP_Voltage_Swing;
      use type DP_Info.DP_Pre_Emph;

      Status : DP_Info.Link_Status;
      CR_Was_Done : constant Boolean := CR_Done;

      pragma Warnings
        (GNATprove, Off, "subprogram ""Dump_Link_Status"" has no effect*",
         Reason => "It's only used for debugging");
      procedure Dump_Link_Status
      is
      begin
         Debug.New_Line;
         Debug.Put_Line ("Link Status:");

         for Lane in DP_Info.Lane_Index range 0
            .. DP_Info.Lane_Index (Lane_Count_As_Integer (Link.Lane_Count) - 1)
         loop
            Debug.Put ("  Lane");
            Debug.Put_Int8 (Int8 (Lane));
            Debug.Put_Line (":");

            Debug.Put_Line ("    CR_Done        : " &
              (if Status.Lanes (Lane).CR_Done         then "1" else "0"));
            Debug.Put_Line ("    Channel_EQ_Done: " &
              (if Status.Lanes (Lane).Channel_EQ_Done then "1" else "0"));
            Debug.Put_Line ("    Symbol_Locked  : " &
              (if Status.Lanes (Lane).Symbol_Locked   then "1" else "0"));
         end loop;

         Debug.Put_Line ("  Interlane_Align_Done: " &
           (if Status.Interlane_Align_Done then "1" else "0"));

         for Lane in DP_Info.Lane_Index range 0
            .. DP_Info.Lane_Index (Lane_Count_As_Integer (Link.Lane_Count) - 1)
         loop
            Debug.Put ("  Adjust");
            Debug.Put_Int8 (Int8 (Lane));
            Debug.Put_Line (":");

            Debug.Put ("    Voltage_Swing: ");
            Debug.Put_Int8 (Int8 (DP_Info.DP_Voltage_Swing'Pos
              (Status.Adjust_Requests (Lane).Voltage_Swing)));
            Debug.New_Line;
            Debug.Put ("    Pre_Emph     : ");
            Debug.Put_Int8 (Int8 (DP_Info.DP_Pre_Emph'Pos
              (Status.Adjust_Requests (Lane).Pre_Emph)));
            Debug.New_Line;
         end loop;

         Debug.New_Line;
      end Dump_Link_Status;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      DP_Info.Read_Link_Status
        (Port     => DP,
         Status   => Status,
         Success  => Success);

      pragma Debug (Success, Dump_Link_Status);

      CR_Done := Success and then DP_Info.All_CR_Done (Status, Link);
      EQ_Done := Success and then DP_Info.All_EQ_Done (Status, Link);
      Success := Success and then (CR_Done or not CR_Was_Done);

      -- Voltage swing may be updated during channel equalization too.
      if Success and not EQ_Done then
         Train_Set.Voltage_Swing :=
            DP_Info.Max_Requested_VS (Status, Link);
         if Train_Set.Voltage_Swing > Max_V_Swing (Port)
         then
            Train_Set.Voltage_Swing := Max_V_Swing (Port);
         end if;
      end if;

      -- According to DP spec, only change preemphasis during channel
      -- equalization. What to do if sink requests it during clock recovery?
      -- Linux always accepts new values from the sink, we too, now: There
      -- are sinks in the wild that need this.
      if Success and not EQ_Done then
         Train_Set.Pre_Emph :=
            DP_Info.Max_Requested_Emph (Status, Link);
         if Train_Set.Pre_Emph > Max_Pre_Emph (Port, Train_Set)
         then
            Train_Set.Pre_Emph := Max_Pre_Emph (Port, Train_Set);
         end if;
      end if;
   end Sink_Adjust_Training;
   pragma Warnings (GNATprove, On, "unused initial value of ""Port""*");

   ----------------------------------------------------------------------------

   procedure Train_DP
     (Port     : in     T;
      Link     : in     DP_Link;
      Success  :    out Boolean)
   is
      use type DP_Info.DP_Voltage_Swing;
      use type DP_Info.DP_Pre_Emph;
      use type Word8;

      DP : constant Aux_T := To_Aux (Port);

      Retries : Natural;
      Max_Retry : constant := 4;
      CR_Done, EQ_Done : Boolean := False;

      EQ_Pattern : constant DP_Info.Training_Pattern :=
        (if TPS3_Supported and Link.Receiver_Caps.TPS3_Supported then
            DP_Info.TP_3
         else
            DP_Info.TP_2);

      Train_Set, Last_Train_Set : DP_Info.Train_Set;

      function CR_Delay return Natural is
         Result : Natural := 100; -- DP spec: 100us
      begin
         if Link.Bandwidth = DP_Bandwidth_5_4 and
            Link.Receiver_Caps.Aux_RD_Interval /= 0
         then
            Result := Natural (Link.Receiver_Caps.Aux_RD_Interval) * 4_000;
         end if;
         return Result;
      end CR_Delay;

      function EQ_Delay return Natural is
         Result : Natural := 400; -- DP spec: 400us
      begin
         if Link.Bandwidth = DP_Bandwidth_5_4 and
            Link.Receiver_Caps.Aux_RD_Interval /= 0
         then
            Result := Natural (Link.Receiver_Caps.Aux_RD_Interval) * 4_000;
         end if;
         return Result;
      end EQ_Delay;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Train_Set.Voltage_Swing := DP_Info.DP_Voltage_Swing'First;
      Train_Set.Pre_Emph      := DP_Info.DP_Pre_Emph'First;

      Set_Pattern (Port, Link, DP_Info.TP_1);
      Set_Signal_Levels (Port, Link, Train_Set);

      pragma Warnings
        (GNATprove, Off, """Success"" modified by call, but value overwritten*",
         Reason => "Read first, then overwritten, looks like a false positive");
      Sink_Init (DP, Link, Success);
      pragma Warnings
        (GNATprove, On, """Success"" modified by call, but value overwritten*");
      if Success then
         Sink_Set_Training_Pattern (DP, Link, DP_Info.TP_1, Success);
      end if;

      if Success then
         Retries := 0;
         for Tries in 1 .. 32 loop
            pragma Loop_Invariant (Retries <= Max_Retry);

            Time.U_Delay (CR_Delay);

            Last_Train_Set := Train_Set;
            Sink_Adjust_Training
              (Port, DP, Link, Train_Set, CR_Done, EQ_Done, Success);
            exit when CR_Done or not Success;

            if Train_Set.Voltage_Swing = Last_Train_Set.Voltage_Swing then
               exit when Retries = Max_Retry;
               Retries := Retries + 1;
            else
               exit when Last_Train_Set.Voltage_Swing = Max_V_Swing (Port);
               Retries := 0;
            end if;

            Set_Signal_Levels (Port, Link, Train_Set);
            Sink_Set_Signal_Levels (Port, DP, Link, Train_Set, Success);
            exit when not Success;
         end loop;
      end if;

      Success := Success and CR_Done;

      if Success then
         Set_Pattern (Port, Link, EQ_Pattern);
         Sink_Set_Training_Pattern (DP, Link, EQ_Pattern, Success);
      end if;

      if Success then
         for Tries in 1 .. 6 loop
            Time.U_Delay (EQ_Delay);

            Sink_Adjust_Training
              (Port, DP, Link, Train_Set, CR_Done, EQ_Done, Success);
            exit when EQ_Done or not Success;

            Set_Signal_Levels (Port, Link, Train_Set);
            Sink_Set_Signal_Levels (Port, DP, Link, Train_Set, Success);
            exit when not Success;
         end loop;
      end if;

      if Success then
         if EQ_Done then
            -- Set_Pattern (TP_None) includes sending the Idle Pattern,
            -- so tell sink first.
            Sink_Set_Training_Pattern
              (DP, Link, DP_Info.TP_None, Success);
         else
            Success := False;
         end if;
      end if;

      if Success then
         Set_Pattern (Port, Link, DP_Info.TP_None);
      else
         Off (Port);
      end if;
   end Train_DP;

end HW.GFX.DP_Training;
