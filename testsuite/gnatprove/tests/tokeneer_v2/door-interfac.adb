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
-- Implementation Notes:
--    None
--
------------------------------------------------------------------
with DoorAPI;
use type DoorAPI.DoorStateT;

package body Door.Interfac
  with SPARK_Mode => Off
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------


   ------------------------------------------------------------------
   -- GetDoorState
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure GetDoorState
     (DoorState : out Door.T;
      Fault     : out Boolean)
   is
      TempState : DoorAPI.DoorStateT := DoorAPI.GetDoorState;
   begin
      if TempState = DoorAPI.Open then
         DoorState := Door.Open;
         Fault     := False;
      elsif TempState = DoorAPI.Closed then
         DoorState := Door.Closed;
         Fault     := False;
      else
         Fault := True;
         DoorState := Door.Open;
      end if;
   end GetDoorState;

end Door.Interfac;
