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

package Floppy
  with Abstract_State => (State,         -- CurrentFile and Presence
                          WrittenState,  -- WrittenFile
                          (Input  with External => Async_Writers),
                          (Output with External => Async_Readers)),
       Initializes => Output
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
   function IsPresent return Boolean
     with Global => State;

   ------------------------------------------------------------------
   -- Write
   --
   -- Description
   --    Writes the supplied file to floppy and deletes the currentFile.
   --
   -- Traceunit: C.Floppy.Write
   -- Traceto : FD.Interfac.UpdateToken
   ------------------------------------------------------------------
   procedure Write (TheFile : in File.T)
     with Global  => (Output => (Output,
                                 WrittenState),
                      In_Out => State),
          Depends => ((Output,
                       WrittenState) => TheFile,
                      State          =>+ null);

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
   procedure Read
     with Global  => (Input  => Input,
                      Output => State),
          Depends => (State => Input);

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
   procedure CheckWrite (WriteOK : out Boolean)
     with Global  => (In_Out => (State,
                                 WrittenState)),
          Depends => ((State,
                       WrittenState) => null,
                      WriteOK        => (State,
                                         WrittenState));

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
   function CurrentFloppy return File.T
     with Global => State;

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
   procedure Init
     with Global  => (Output => (State,
                                 WrittenState)),
          Depends => ((State,
                       WrittenState) => null);

end Floppy;
