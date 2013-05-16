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

with Keyboard.Interface;
with BasicTypes;
use type BasicTypes.PresenceT;

package body Keyboard
--# own Input is in Keyboard.Interface.Input;
is

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --   None.
   ------------------------------------------------------------------

   procedure Init
   --# global in Interface.Input;
   --# derives null from Interface.Input;
   is
   begin
      Interface.Init;
   end Init;

   ------------------------------------------------------------------
   -- Finalise
   --
   -- Implementation Notes:
   --   None.
   ------------------------------------------------------------------

   procedure Finalise
   --# global in Interface.Input;
   --# derives null from Interface.Input;
   is
   begin
      Interface.Finalise;
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
   --# global in Interface.Input;
   --# derives DataPresence,
   --#         Data         from Interface.Input;
   is
      LocalData : DataTextT;
      LocalLength : DataLengthT;

   begin

      Interface.ReadKeyboardData(KeyedDataPresence => DataPresence,
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
   --# global in Interface.Input;
   --# derives null from Interface.Input;
   is
   begin
      Interface.Poll;
   end Poll;


end Keyboard;
