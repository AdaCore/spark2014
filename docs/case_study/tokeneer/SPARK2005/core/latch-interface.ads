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
-- Latch.Interface
--
-- Description:
--    Provides interface to the physical latch, via calls to the
--    Latch API.
--
------------------------------------------------------------------

private package Latch.Interface
--# own out Output : OutType;
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   --# type OutType is Abstract;
   --# function prf_isLocked(Output : OutType) return Boolean;

   ------------------------------------------------------------------
   -- Lock
   --
   -- Description:
   --    Locks the latch
   --
   ------------------------------------------------------------------

   procedure Lock(Fault :    out Boolean);
   --# global    out Output;
   --# derives Output,
   --#         Fault  from ;
   --# post prf_isLocked(Output) or Fault;


   ------------------------------------------------------------------
   -- Unlock
   --
   -- Description:
   --    Unlocks the latch
   --
   ------------------------------------------------------------------

   procedure Unlock(Fault :    out Boolean);
   --# global    out Output;
   --# derives Output,
   --#         Fault  from ;
   --# post not prf_isLocked(Output) or Fault;

end Latch.Interface;
