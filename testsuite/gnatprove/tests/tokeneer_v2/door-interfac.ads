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
-- Door.Interfac
--
-- Description:
--    Provides interface to the physical door.
--
------------------------------------------------------------------

private package Door.Interfac
  with SPARK_Mode,
       Abstract_State => (Input with External => Async_Writers,
                                     Part_Of  => Door.Input)
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
                           Fault      :    out Boolean)
     with Global  => (Input  => Input),
          Depends => ((DoorState,
                       Fault) => Input);

end Door.Interfac;
