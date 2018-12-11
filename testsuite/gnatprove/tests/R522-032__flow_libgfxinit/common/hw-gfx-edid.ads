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

package HW.GFX.EDID
is

   use type Word8;
   use type Word16;

   subtype Raw_EDID_Index is Natural range 0 .. 127;
   subtype Raw_EDID_Data is Buffer (Raw_EDID_Index);

   function Valid (Raw_EDID : Raw_EDID_Data) return Boolean;
   procedure Sanitize (Raw_EDID : in out Raw_EDID_Data; Success : out Boolean)
   with
      Post => (if Success then Valid (Raw_EDID));

   DESCRIPTOR_1 : constant := 54;

   function Read_LE16
     (Raw_EDID : Raw_EDID_Data;
      Offset   : Raw_EDID_Index)
      return Word16
   with
      Pre => Offset < Raw_EDID_Index'Last;

   function Compatible_Display
     (Raw_EDID : Raw_EDID_Data;
      Display  : Display_Type)
      return Boolean
   with
      Pre => Valid (Raw_EDID);

   function Has_Preferred_Mode (Raw_EDID : Raw_EDID_Data) return Boolean is
     (Int64 (Read_LE16 (Raw_EDID, DESCRIPTOR_1)) * 10_000 in Frequency_Type and
      ( Raw_EDID (DESCRIPTOR_1 +  2) /= 0 or
       (Raw_EDID (DESCRIPTOR_1 +  4) and 16#f0#) /= 0) and
      ( Raw_EDID (DESCRIPTOR_1 +  8) /= 0 or
       (Raw_EDID (DESCRIPTOR_1 + 11) and 16#c0#) /= 0) and
      ( Raw_EDID (DESCRIPTOR_1 +  9) /= 0 or
       (Raw_EDID (DESCRIPTOR_1 + 11) and 16#30#) /= 0) and
      ( Raw_EDID (DESCRIPTOR_1 +  3) /= 0 or
       (Raw_EDID (DESCRIPTOR_1 +  4) and 16#0f#) /= 0) and
      ( Raw_EDID (DESCRIPTOR_1 +  5) /= 0 or
       (Raw_EDID (DESCRIPTOR_1 +  7) and 16#f0#) /= 0) and
      ((Raw_EDID (DESCRIPTOR_1 + 10) and 16#f0#) /= 0 or
       (Raw_EDID (DESCRIPTOR_1 + 11) and 16#0c#) /= 0) and
      ((Raw_EDID (DESCRIPTOR_1 + 10) and 16#0f#) /= 0 or
       (Raw_EDID (DESCRIPTOR_1 + 11) and 16#03#) /= 0) and
      ( Raw_EDID (DESCRIPTOR_1 +  6) /= 0 or
       (Raw_EDID (DESCRIPTOR_1 +  7) and 16#0f#) /= 0))
   with
      Pre => Valid (Raw_EDID);
   function Preferred_Mode (Raw_EDID : Raw_EDID_Data) return Mode_Type
   with
      Pre => Valid (Raw_EDID) and then Has_Preferred_Mode (Raw_EDID);

end HW.GFX.EDID;
