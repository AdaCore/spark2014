--
-- Copyright (C) 2016 secunet Security Networks AG
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

with HW.Debug;
with GNAT.Source_Info;

use type HW.Byte;
use type HW.Word16;

package body HW.GFX.EDID is

   subtype Header_Index is Raw_EDID_Index range 0 .. 7;
   type Header_Type is new Buffer (Header_Index);
   Header_Pattern : constant Header_Type :=
     (16#00#, 16#ff#, 16#ff#, 16#ff#, 16#ff#, 16#ff#, 16#ff#, 16#00#);

   function Checksum_Valid (Raw_EDID : Raw_EDID_Data) return Boolean
   with
      Pre => True
   is
      Sum : Byte := 16#00#;
   begin
      for I in Raw_EDID_Index loop
         Sum := Sum + Raw_EDID (I);
      end loop;
      pragma Debug (Sum /= 16#00#, Debug.Put_Line
        (GNAT.Source_Info.Enclosing_Entity & ": EDID checksum invalid!"));
      return Sum = 16#00#;
   end Checksum_Valid;

   function Header_Score (Raw_EDID : Raw_EDID_Data) return Natural
   is
      Score : Natural := 0;
   begin
      for I in Header_Index loop
         pragma Loop_Invariant (Score <= I);
         if Raw_EDID (I) = Header_Pattern (I) then
            Score := Score + 1;
         end if;
      end loop;
      return Score;
   end Header_Score;

   function Valid (Raw_EDID : Raw_EDID_Data) return Boolean
   is
   begin
      return Header_Score (Raw_EDID) = 8 and then Checksum_Valid (Raw_EDID);
   end Valid;

   procedure Sanitize (Raw_EDID : in out Raw_EDID_Data; Success : out Boolean)
   is
      Score : constant Natural := Header_Score (Raw_EDID);
   begin
      pragma Debug (Score /= 8, Debug.Put_Line
        (GNAT.Source_Info.Enclosing_Entity & ": EDID header pattern mismatch!"));

      if Score = 6 or Score = 7 then
         pragma Debug (Debug.Put_Line
           (GNAT.Source_Info.Enclosing_Entity & ": Trying to fix up."));
         Raw_EDID (Header_Index) := Buffer (Header_Pattern);
      end if;

      Success := Valid (Raw_EDID);
   end Sanitize;

   ----------------------------------------------------------------------------

   REVISION                            : constant :=         19;
   INPUT                               : constant :=         20;
   INPUT_DIGITAL                       : constant := 1 * 2 ** 7;
   INPUT_DIGITAL_DEPTH_SHIFT           : constant :=          4;
   INPUT_DIGITAL_DEPTH_MASK            : constant := 7 * 2 ** 4;
   INPUT_DIGITAL_DEPTH_UNDEF           : constant := 0 * 2 ** 4;
   INPUT_DIGITAL_DEPTH_RESERVED        : constant := 7 * 2 ** 4;

   ----------------------------------------------------------------------------

   function Compatible_Display
     (Raw_EDID : Raw_EDID_Data;
      Display  : Display_Type)
      return Boolean
   is
   begin
      return (Display = VGA) = ((Raw_EDID (INPUT) and INPUT_DIGITAL) = 16#00#);
   end Compatible_Display;

   function Read_LE16
     (Raw_EDID : Raw_EDID_Data;
      Offset   : Raw_EDID_Index)
      return Word16
   is
   begin
      return Shift_Left (Word16 (Raw_EDID (Offset + 1)), 8) or
             Word16 (Raw_EDID (Offset));
   end Read_LE16;

   function Preferred_Mode (Raw_EDID : Raw_EDID_Data) return Mode_Type
   is
      Base : constant := DESCRIPTOR_1;
      Mode : Mode_Type;

      function Read_12
        (Lower_8, Upper_4  : Raw_EDID_Index;
         Shift             : Natural)
         return Word16 is
        (             Word16 (Raw_EDID (Lower_8)) or
         (Shift_Left (Word16 (Raw_EDID (Upper_4)), Shift) and 16#0f00#));

      function Read_10
        (Lower_8, Upper_2  : Raw_EDID_Index;
         Shift             : Natural)
         return Word16 is
        (             Word16 (Raw_EDID (Lower_8)) or
         (Shift_Left (Word16 (Raw_EDID (Upper_2)), Shift) and 16#0300#));

      function Read_6
        (Lower_4     : Raw_EDID_Index;
         Lower_Shift : Natural;
         Upper_2     : Raw_EDID_Index;
         Upper_Shift : Natural)
         return Word8 is
        ((Shift_Right (Word8 (Raw_EDID (Lower_4)), Lower_Shift) and 16#0f#) or
         (Shift_Left  (Word8 (Raw_EDID (Upper_2)), Upper_Shift) and 16#30#));
   begin
      Mode := Mode_Type'
        (Dotclock             => Pos64 (Read_LE16 (Raw_EDID, Base)) * 10_000,
         H_Visible            => Width_Type (Read_12 (Base +  2, Base +  4, 4)),
         H_Sync_Begin         => Width_Type (Read_10 (Base +  8, Base + 11, 2)),
         H_Sync_End           => Width_Type (Read_10 (Base +  9, Base + 11, 4)),
         H_Total              => Width_Type (Read_12 (Base +  3, Base +  4, 8)),
         V_Visible            => Height_Type (Read_12 (Base +  5, Base +  7, 4)),
         V_Sync_Begin         => Height_Type (Read_6  (Base + 10, 4, Base + 11, 2)),
         V_Sync_End           => Height_Type (Read_6  (Base + 10, 0, Base + 11, 4)),
         V_Total              => Height_Type (Read_12 (Base +  6, Base +  7, 8)),
         H_Sync_Active_High   => (Raw_EDID (Base + 17) and 16#02#) /= 0,
         V_Sync_Active_High   => (Raw_EDID (Base + 17) and 16#04#) /= 0,
         BPC                  =>
           (if Raw_EDID (REVISION) < 4 or
               (Raw_EDID (INPUT) and INPUT_DIGITAL) = 16#00# or
               (Raw_EDID (INPUT) and INPUT_DIGITAL_DEPTH_MASK) = INPUT_DIGITAL_DEPTH_UNDEF or
               (Raw_EDID (INPUT) and INPUT_DIGITAL_DEPTH_MASK) = INPUT_DIGITAL_DEPTH_RESERVED
            then
               Auto_BPC
            else
               4 + 2 * Pos64 (Shift_Right
                 (Raw_EDID (INPUT) and INPUT_DIGITAL_DEPTH_MASK,
                  INPUT_DIGITAL_DEPTH_SHIFT))));

      -- Calculate absolute values from EDID relative values.
      Mode.H_Sync_Begin := Mode.H_Visible    + Mode.H_Sync_Begin;
      Mode.H_Sync_End   := Mode.H_Sync_Begin + Mode.H_Sync_End;
      Mode.H_Total      := Mode.H_Visible    + Mode.H_Total;
      Mode.V_Sync_Begin := Mode.V_Visible    + Mode.V_Sync_Begin;
      Mode.V_Sync_End   := Mode.V_Sync_Begin + Mode.V_Sync_End;
      Mode.V_Total      := Mode.V_Visible    + Mode.V_Total;

      return Mode;
   end Preferred_Mode;

end HW.GFX.EDID;
