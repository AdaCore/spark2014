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
-- Poll
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
package body Poll is

   ------------------------------------------------------------------
   -- Activity
   --
   -- Implementation Notes:
   --
   --    Note that polling the biometric device is not done here
   --    it is only polled when the system is waiting to read the
   --    device so appears as part of the WaitingFinger activity.
   --
   --    Note that polling the floppy is not done here
   --    it is only polled when the system needs a floppy to be present.
   ------------------------------------------------------------------
   procedure Activity (SystemFault :    out Boolean)
   is
   begin
      Clock.Poll;
      Door.Poll(SystemFault => SystemFault);
      UserToken.Poll;
      AdminToken.Poll;
      UserEntry.DisplayPollUpdate;
      Keyboard.Poll;
   end Activity;

end Poll;
