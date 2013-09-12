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
-- Door.Interfac
--
-- Description:
--    Provides interface to the physical door.
--
------------------------------------------------------------------
--# inherit Door;

private package Door.Interfac
--# own in     Input;
is pragma SPARK_Mode (On);

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

end Door.Interfac;
