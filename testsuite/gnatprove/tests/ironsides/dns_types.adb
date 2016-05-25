----------------------------------------------------------------
-- IRONSIDES - DNS SERVER
--
-- By: Martin C. Carlisle and Barry S. Fagin
--     Department of Computer Science
--     United States Air Force Academy
--
-- Modified by: Altran UK Limited
--
-- This is free software; you can redistribute it and/or
-- modify without restriction.  We do ask that you please keep
-- the original author information, and clearly indicate if the
-- software has been modified.
--
-- This software is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
----------------------------------------------------------------

with Gnat.Byte_Swapping;

package body DNS_Types is

   function Byte_Swap_US(U : Unsigned_Short) return Unsigned_Short
     with SPARK_Mode => Off
   is
      Answer : Unsigned_Short;
   begin
      Answer := U;
      Gnat.Byte_Swapping.Swap2 (Answer'Address);
      return Answer;
   end Byte_Swap_US;

   ---------------
   -- Byte_Swap --
   ---------------

   procedure Byte_Swap (H : in out Header_Type) is
   begin
      H.MessageID := Byte_Swap_US (H.MessageID);
      H.QDCount   := Byte_Swap_US (H.QDCount);
      H.ANCount   := Byte_Swap_US (H.ANCount);
      H.NSCount   := Byte_Swap_US (H.NSCount);
      H.ARCount   := Byte_Swap_US (H.ARCount);
   end Byte_Swap;

end DNS_Types;
