------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- LatchAPI
--
-- Description:
--    Provides operation to control the portal latch.
--
------------------------------------------------------------------

package LatchAPI is

   ------------------------------------------------------------------
   -- Unlock
   --
   -- Description:
   --    Sends a request to unlock the latch immediately.
   --    Note that the Unlock procedure does not attempt to lock the latch
   --    after a timeout period. The lock procedure will need to be called
   --    after the specified timeout has occurred.
   --    Failed is returned if the operation was not successful.
   --
   ------------------------------------------------------------------
   procedure Unlock(Failed : out Boolean);

   ------------------------------------------------------------------
   -- Lock
   --
   -- Description:
   --    Sends a request to lock the latch immediately.
   --    Failed is returned if the operation was not successful.
   --
   ------------------------------------------------------------------
   procedure Lock(Failed : out Boolean);

end LatchAPI;
