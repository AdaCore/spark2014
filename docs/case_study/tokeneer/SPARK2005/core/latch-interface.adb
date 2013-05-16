------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- Latch.Interface
--
-- Implementation Notes:
--    None
--
------------------------------------------------------------------
with LatchAPI;

package body Latch.Interface
is

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

   procedure Lock(Fault :    out Boolean)
   is
   begin
      LatchAPI.Lock(Failed => Fault);
   end Lock;

   ------------------------------------------------------------------
   -- Unlock
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------

   procedure Unlock(Fault :    out Boolean)
   is
   begin
      LatchAPI.Unlock(Failed => Fault);
   end Unlock;

end Latch.Interface;
