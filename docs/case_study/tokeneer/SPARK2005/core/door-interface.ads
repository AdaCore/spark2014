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
-- Door.Interface
--
-- Description:
--    Provides interface to the physical door.
--
------------------------------------------------------------------
--# inherit Door;

private package Door.Interface
--# own in     Input;
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------


   ------------------------------------------------------------------
   -- GetDoorState
   --
   -- Description:
   --    Polls the physical door.
   --
   ------------------------------------------------------------------

   procedure GetDoorState (DoorState  :    out Door.T;
                           Fault      :    out Boolean);
   --# global in     Input;
   --# derives DoorState,
   --#         Fault      from Input;

end Door.Interface;
