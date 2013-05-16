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
-- Floppy
--
-- Description:
--    Package interfacing to the Floppy Drive.
--
------------------------------------------------------------------

with File;
--# inherit File;

package Floppy
--# own
--#         State,         -- CurrentFile and Presence
--#         WrittenState,  -- WrittenFile
--#  in     Input,
--#     out Output;
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- IsPresent
   --
   -- Description
   --    Returns True exactly when there is a floppy present.
   --
   -- Traceunit: C.Floppy.IsPresent
   -- Traceto : FD.RealWorld.State
   ------------------------------------------------------------------
   function IsPresent return Boolean;
   --# global State;

   ------------------------------------------------------------------
   -- Write
   --
   -- Description
   --    Writes the supplied file to floppy and deletes the currentFile.
   --
   -- Traceunit: C.Floppy.Write
   -- Traceto : FD.Interface.UpdateToken
   ------------------------------------------------------------------
   procedure Write(TheFile : in File.T);
   --# global in out State;
   --#           out Output;
   --#           out WrittenState;
   --# derives Output,
   --#         WrittenState from TheFile &
   --#         State        from *;


   ------------------------------------------------------------------
   -- Read
   --
   -- Description
   --    Reads the file from floppy. Note the first file is read.
   --
   -- Traceunit: C.Floppy.Read
   -- Traceto : FD.Enclave.ReadEnrolmentFloppy
   -- Traceto : FD.Enclave.FinishArchiveLogOK
   -- Traceto : FD.Enclave.FinishArchiveLogBadMatch
   -- Traceto : FD.Enclave.StartUpdateConfigDataOK
   ------------------------------------------------------------------
   procedure Read;
   --# global in     Input;
   --#           out State;
   --# derives State from Input;

   ------------------------------------------------------------------
   -- CheckWrite
   --
   -- Description
   --    Returns true if the current floppy matches the last written
   --    floppy. False otherwise.
   --
   -- Traceunit: C.Floppy.CheckWrite
   -- Traceto : FD.Enclave.FinishArchiveLogOK
   -- Traceto : FD.Enclave.FinishArchiveLogBadMatch
   ------------------------------------------------------------------
   procedure CheckWrite (WriteOK : out Boolean);
   --# global in out State;
   --#        in out WrittenState;
   --# derives State,
   --#         WrittenState from  &
   --#         WriteOK      from State,
   --#                           WrittenState;

   ------------------------------------------------------------------
   -- CurrentFloppy
   --
   -- Description
   --    Returns the current file on Floppy. If there is no file a
   --    null file is returned.
   --
   -- Traceunit: C.Floppy.CurrentFloppy
   -- Traceto : FD.RealWorld.State
   ------------------------------------------------------------------
   function CurrentFloppy return File.T;
   --# global State;

   ------------------------------------------------------------------
   -- Init
   --
   -- Description
   --    Initialises the Floppy state.
   --    Also establishes the drive letter and creates
   --    a temporary directory if required.
   --
   -- Traceunit: C.Floppy.Init
   -- Traceto : FD.TIS.TISStartup
   ------------------------------------------------------------------
   procedure Init;
   --# global out State;
   --#        out WrittenState;
   --# derives State,
   --#         WrittenState from ;

end Floppy;
