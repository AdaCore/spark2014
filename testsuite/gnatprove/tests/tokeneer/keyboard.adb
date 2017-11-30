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
-- Keyboard
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------

with Keyboard.Interfac;
with CommonTypes;
use type CommonTypes.PresenceT;

package body Keyboard
  with Refined_State => (Inputs => Keyboard.Interfac.Inputs)
is

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --   None.
   ------------------------------------------------------------------
   procedure Init
     with Refined_Global  => (Input  => Interfac.Inputs),
          Refined_Depends => (null => Interfac.Inputs)
   is
   begin
      Interfac.Init;
   end Init;

   ------------------------------------------------------------------
   -- Finalise
   --
   -- Implementation Notes:
   --   None.
   ------------------------------------------------------------------
   procedure Finalise
     with Refined_Global  => (Input  => Interfac.Inputs),
          Refined_Depends => (null => Interfac.Inputs)
   is
   begin
      Interfac.Finalise;
   end Finalise;

   ------------------------------------------------------------------
   -- Read
   --
   -- Implementation Notes:
   --   None.
   ------------------------------------------------------------------
   procedure Read (DataPresence :    out CommonTypes.PresenceT;
                   Data         :    out DataT)
     with Refined_Global  => (Input  => Interfac.Inputs),
          Refined_Depends => ((Data,
                               DataPresence) => Interfac.Inputs)
   is
      LocalData   : DataTextT;
      LocalLength : DataLengthT;
   begin

      Interfac.ReadKeyboardData(KeyedDataPresence => DataPresence,
                                 KeyedData         => LocalData,
                                 KeyedDataLength   => LocalLength);

      Data := DataT'(Length => LocalLength,
                     Text   => LocalData);
   end Read;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Implementation Notes:
   --   None.
   ------------------------------------------------------------------
   procedure Poll
     with Refined_Global  => (Input  => Interfac.Inputs),
          Refined_Depends => (null => Interfac.Inputs)
   is
   begin
      Interfac.Poll;
   end Poll;

end Keyboard;
