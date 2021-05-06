------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

package Enclave
  with Abstract_State => State
is
   type StatusT is (EnclaveQuiescent);

   procedure Init
     with Global => (Output => State);


private
   Status : StatusT with Part_Of => State;

end Enclave;
