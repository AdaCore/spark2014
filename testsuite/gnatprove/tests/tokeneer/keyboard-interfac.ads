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
-- Keyboard.Interfac
--
-- Description:
--    Provides the interface to the console for reading keyed data.
--
------------------------------------------------------------------
with CommonTypes;
with Keyboard;

private package Keyboard.Interfac
  with Abstract_State => (Inputs with External => Async_Writers,
                                      Part_Of  => Keyboard.Inputs)
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
     (KeyedDataPresence : out CommonTypes.PresenceT;
      KeyedData         : out Keyboard.DataTextT;
      KeyedDataLength   : out Keyboard.DataLengthT)
     with Global  => (Input  => Inputs),
          Depends => ((KeyedData,
                       KeyedDataLength,
                       KeyedDataPresence) => Inputs);

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initialises the keyboard polling mechanism.
   --
   ------------------------------------------------------------------
   procedure Init
     with Global  => (Input  => Inputs),
          Depends => (null => Inputs);

   ------------------------------------------------------------------
   -- Finalise
   --
   -- Description:
   --    Finalises the keyboard polling mechanism.
   --
   ------------------------------------------------------------------
   procedure Finalise
     with Global  => (Input  => Inputs),
          Depends => (null => Inputs);

   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Polls the keyboard checking the freshness of data.
   --
   ------------------------------------------------------------------
   procedure Poll
     with Global  => (Input  => Inputs),
          Depends => (null => Inputs);

end Keyboard.Interfac;
