------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency.All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd.under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- Latch.Interfac
--
-- Implementation Notes:
--    None
--
------------------------------------------------------------------
with LatchAPI;

package body Latch.Interfac
  with SPARK_Mode => Off
is

   Locked : Boolean;

   function isLocked return Boolean is (Locked);

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Lock
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Lock (Fault : out Boolean) is
   begin
      LatchAPI.Lock (Failed => Fault);
      if not Fault then
         Locked := True;
      end if;
   end Lock;

   ------------------------------------------------------------------
   -- Unlock
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Unlock (Fault : out Boolean) is
   begin
      LatchAPI.Unlock (Failed => Fault);

      if not Fault then
         Locked := False;
      end if;
   end Unlock;

end Latch.Interfac;
