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
-- Latch.Interfac
--
-- Description:
--    Provides interface to the physical latch, via calls to the
--    Latch API.
--
------------------------------------------------------------------

private package Latch.Interfac
  with SPARK_Mode,
       Abstract_State => (Output with External => Async_Readers,
                                      Part_Of  => Latch.Output)
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   --  Proof function
   function isLocked return Boolean
     with Global     => null,
          Ghost;

   ------------------------------------------------------------------
   -- Lock
   --
   -- Description:
   --    Locks the latch
   --
   ------------------------------------------------------------------
   procedure Lock (Fault :    out Boolean)
     with Global  => (Output => Output),
          Depends => ((Fault,
                       Output) => null),
          Post    => isLocked or Fault;

   ------------------------------------------------------------------
   -- Unlock
   --
   -- Description:
   --    Unlocks the latch
   --
   ------------------------------------------------------------------
   procedure Unlock (Fault :    out Boolean)
     with Global  => (Output => Output),
          Depends => ((Fault,
                       Output) => null),
          Post    => not isLocked or Fault;

end Latch.Interfac;
