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
-- Description:
--    Provides facitities for reading the keyboard.
--
------------------------------------------------------------------
with BasicTypes;
--# inherit BasicTypes;

package Keyboard
--# own in Input;
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   MaxDataLength : constant Positive := 78;
   subtype DataLengthT is Natural range 0 .. MaxDataLength;
   subtype DataI is Positive range 1..MaxDataLength;
   subtype DataTextT is String(DataI);

   type DataT is
      record
         Length : DataLengthT;
         Text   : DataTextT;
      end record;

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initialises the keyboard polling mechanism.
   --
   -- Traceunit: C.Keyboard.Init
   -- Traceto:  FD.TIS.TISStartup
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
   -- Traceunit: C.Keyboard.Finalise
   ------------------------------------------------------------------

   procedure Finalise;
   --# global in Input;
   --# derives null from Input;


   ------------------------------------------------------------------
   -- Read
   --
   -- Description:
   --    Reads the latest input from the keyboard.
   --
   -- Traceunit: C.Keyboard.Read
   -- Traceto: FD.Poll.Keyboard
   -- Traceto: FD.Enclave.ValidateOpRequestOK
   -- Traceto: FD.Enclave.ValidateOpRequestFail
   ------------------------------------------------------------------

   procedure Read
     (DataPresence :    out BasicTypes.PresenceT;
      Data         :    out DataT );
   --# global in Input;
   --# derives DataPresence,
   --#         Data         from Input;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Checks the freshness of keyboard data.
   --
   -- Traceunit: C.Keyboard.Poll
   -- Traceto: FD.Poll.Keyboard
   ------------------------------------------------------------------

   procedure Poll;
   --# global in Input;
   --# derives null from Input;



end Keyboard;
