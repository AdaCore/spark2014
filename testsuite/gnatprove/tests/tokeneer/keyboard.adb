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
-- Keyboard
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------

with Keyboard.Interfac;
with BasicTypes;
use type BasicTypes.PresenceT;

package body Keyboard
--# own Input is in Keyboard.Interfac.Input;
is pragma SPARK_Mode (On);

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --   None.
   ------------------------------------------------------------------

   procedure Init
   --# global in Interfac.Input;
   --# derives null from Interfac.Input;
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
   --# global in Interfac.Input;
   --# derives null from Interfac.Input;
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

   procedure Read
     (DataPresence :    out BasicTypes.PresenceT;
      Data         :    out DataT )
   --# global in Interfac.Input;
   --# derives DataPresence,
   --#         Data         from Interfac.Input;
   is
      LocalData : DataTextT;
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
   --# global in Interfac.Input;
   --# derives null from Interfac.Input;
   is
   begin
      Interfac.Poll;
   end Poll;


end Keyboard;
