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
-- Keyboard.Interfac
--
-- Implementation Notes:
--    Not SPARK as it uses a task to allow polling.
--
------------------------------------------------------------------
with Interfaces.C;
with Ada.Characters.Latin_1;
with Ada.Characters.Handling;

with System;

package body Keyboard.Interfac
  with SPARK_Mode => Off
is

   --PromptCoord : constant Win32.WinCon.Coord := (2, 4);

   ----------------------------------------------------------------------
   -- KeyedDataStore Protected Object
   --
   -- Description:
   --    This protected object provides a shared data repository for
   --    the Keyboard reader Task and the remainder of the system.
   --    The Reader Task Sets the value of KeyedData, the remainder
   --    of the system can then read the values.
   --
   ---------------------------------------------------------------------
   protected KeyedDataStore is

      ----------------------------------------------------------------------
      -- SetData
      --
      -- Description:
      --    Adds Keyed Data to the Store.
      --
      ---------------------------------------------------------------------
      procedure SetData (KeyedData : in Keyboard.DataTextT;
                         Length    : in Natural);

      ----------------------------------------------------------------------
      -- GetData
      --
      -- Description:
      --    Reads Keyed Data from the Store and clears the currently
      --    held Keyed Data so it is not read twice.
      --
      ---------------------------------------------------------------------
      procedure GetData (KeyedData : out Keyboard.DataTextT;
                         Length    : out Keyboard.DataLengthT;
                         Presence  : out CommonTypes.PresenceT);

      ----------------------------------------------------------------------
      -- Refresh
      --
      -- Description:
      --    Refreshes the data if it becomes too old.
      --
      ---------------------------------------------------------------------
      procedure Refresh;

   private
      TheData     : Keyboard.DataTextT := (others => ' ');
      TheLength   : Keyboard.DataLengthT := 0;
      ThePresence : CommonTypes.PresenceT := CommonTypes.Absent;
      IsFresh     : Boolean := False;
   end KeyedDataStore;

   ----------------------------------------------------------------------
   -- KeyedDataStore Protected Object
   --
   -- Implementation Notes:
   --     None.
   --
   ---------------------------------------------------------------------
   protected body KeyedDataStore is

      ----------------------------------------------------------------------
      -- SetData
      --
      -- Implementation Notes:
      --    Removes the CR and LF from the end of the read data.
      --    A blank line with no characters other than <Return>
      --    will not count at present data.
      ---------------------------------------------------------------------
      procedure SetData (KeyedData : in Keyboard.DataTextT;
                         Length    : in Natural)
      is
      begin
         TheData := KeyedData;
         if Length <= Keyboard.DataLengthT'Last then
            TheLength := Length;
         else
            TheLength := Keyboard.DataLengthT'Last;
         end if;

         -- Remove the CR & LF. A blank line does not count as present data.
         if TheLength > 2 then
            ThePresence := CommonTypes.Present;
            TheLength := TheLength - 2;
            IsFresh := True;
         else
            ThePresence := CommonTypes.Absent;
            TheLength := 0;
         end if;

      end SetData;

      ----------------------------------------------------------------------
      -- GetData
      --
      -- Implementation Notes:
      --    None.
      --
      ---------------------------------------------------------------------
      procedure GetData (KeyedData : out Keyboard.DataTextT;
                         Length    : out Keyboard.DataLengthT;
                         Presence  : out CommonTypes.PresenceT) is
      begin
         KeyedData := TheData;
         Length := TheLength;
         Presence := ThePresence;

         ThePresence := CommonTypes.Absent;
         TheLength := 0;

      end GetData;

      ----------------------------------------------------------------------
      -- Refresh
      --
      -- Implementation Notes:
      --    None.
      --
      ---------------------------------------------------------------------
      procedure Refresh is
      begin
         if not IsFresh then
            TheData := (others => ' ');
            ThePresence := CommonTypes.Absent;
            TheLength := 0;
         else
            IsFresh := False;
         end if;
      end Refresh;

   end KeyedDataStore;


   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ----------------------------------------------------------------------
   -- Reader Task
   --
   -- Description:
   --    This task encapsulates the process of reading the keyboard.
   --    It is required due to the blocking nature of the console read.
   --    Once Started it will continually read the Keyboard, placing the
   --    latest command in the KeyedDataStore.
   --    The Stop Entry allows task termination.
   --
   -- Implementation Notes:
   --    None.
   ---------------------------------------------------------------------

   task Reader is
      entry Start;
      entry Stop;
   end;

   ----------------------------------------------------------------------
   -- Read
   --
   -- Description:
   --    This operation reads a line from the Win32 Console. The operation
   --    blocks until the user presses <return>.
   --
   -- Implementation Notes:
   --    None.
   ---------------------------------------------------------------------
   procedure Read
     (Buffer : out String;
      Len    : out Natural;
      OK     : out Boolean)
   is
      pragma Unreferenced (Buffer);
   begin
      OK := True;
      Len := 0;
   end Read;

   ----------------------------------------------------------------------
   -- Reader Task
   --
   -- Implementation Notes:
   --    None.
   ---------------------------------------------------------------------
   task body Reader is
      ReadData   : Keyboard.DataTextT;
      DataLength : Natural;
      ReadOK     : Boolean;
   begin
      select
         accept Start;
         loop
            select
               accept Stop;
               exit;
            else
               Read(ReadData, DataLength, ReadOK);
               if ReadOK then
                  KeyedDataStore.SetData(ReadData, DataLength);
               end if;
            end select;
         end loop;
      or
         terminate;
      end select;
   end Reader;

   ------------------------------------------------------------------
   -- ReadKeyboardData
   --
   -- Implementation Notes:
   --    Converts to Upper case so that checks are case insensitive.
   --
   ------------------------------------------------------------------

   procedure ReadKeyboardData
     (KeyedDataPresence : out CommonTypes.PresenceT;
      KeyedData         : out Keyboard.DataTextT;
      KeyedDataLength   : out Keyboard.DataLengthT)
   is
      LocalKeyedData : Keyboard.DataTextT;

   begin
      KeyedData := (others => ' ');

      KeyedDataStore.GetData
        (LocalKeyedData,
         KeyedDataLength,
         KeyedDataPresence);

      if KeyedDataLength > 0 then
         for I in DataI range 1 .. KeyedDataLength loop
            KeyedData(I) :=
              Ada.Characters.Handling.To_Upper(LocalKeyedData(I));
         end loop;
      end if;
   end ReadKeyboardData;

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Init is
   begin
      Reader.Start;
   end Init;

   ------------------------------------------------------------------
   -- Finalise
   --
   -- Implementation Notes:
   --    In order to force the current Win32.WinCon.Read to terminate
   --    we destroy the console.
   --    It is then possible to stop the Reader Task.
   --
   ------------------------------------------------------------------
   procedure Finalise is
   begin
      Reader.Stop;
   end Finalise;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Poll is
   begin
      KeyedDataStore.Refresh;
   end Poll;

end Keyboard.Interfac;
