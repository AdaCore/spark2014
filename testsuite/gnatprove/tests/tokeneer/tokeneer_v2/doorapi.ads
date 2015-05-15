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
-- DoorAPI
--
-- Description:
--    The interface with the door. Provides operation to monitor the state of
--    door.
--
------------------------------------------------------------------

package DoorAPI is

   ------------------------------------------------------------------
   --
   -- Types
   --
   ------------------------------------------------------------------

   -- Enumerated type to model the state of the Door.

   type DoorStateT is (Error, Open, Closed);

   ------------------------------------------------------------------
   -- GetDoorState
   --
   -- Description:
   --    A means of 'polling' the door to determine the state of the door.
   --    If erroneous data is returned, or there is a problem with server
   --    comms, then Error is returned.
   --
   ------------------------------------------------------------------
   function GetDoorState return DoorStateT
     with Global => null;

end DoorAPI;
