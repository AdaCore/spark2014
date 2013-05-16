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
-- Keyboard.Interface
--
-- Description:
--    Provides the interface to the console for reading keyed data.
--
------------------------------------------------------------------
with BasicTypes;
with Keyboard;
--# inherit BasicTypes,
--#         Keyboard;

private package Keyboard.Interface
--# own in Input;
is

   ------------------------------------------------------------------
   -- ReadKeyboardData
   --
   -- Description:
   --    Reads the data from the keyboard, if no data is present
   --    this is indicated by the value of KeyedDataPresence.
   --
   ------------------------------------------------------------------

   procedure ReadKeyboardData
     (KeyedDataPresence : out BasicTypes.PresenceT;
      KeyedData         : out Keyboard.DataTextT;
      KeyedDataLength   : out Keyboard.DataLengthT);
   --# global in Input;
   --# derives KeyedDataPresence,
   --#         KeyedData,
   --#         KeyedDataLength   from Input;

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initialises the keyboard polling mechanism.
   --
   ------------------------------------------------------------------
   procedure Init;
   --# global in Input;
   --# derives null from Input;

   ------------------------------------------------------------------
   -- Finalise
   --
   -- Description:
   --    Finalises the keyboard polling mechanism.
   --
   ------------------------------------------------------------------
   procedure Finalise;
   --# global in Input;
   --# derives null from Input;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Polls the keyboard checking the freshness of data.
   --
   ------------------------------------------------------------------
   procedure Poll;
   --# global in Input;
   --# derives null from Input;

end Keyboard.Interface;
