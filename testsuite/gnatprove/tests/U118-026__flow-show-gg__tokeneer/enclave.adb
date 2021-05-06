------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

package body Enclave
  with Refined_State => (State => Status)
is
   procedure Init
     --  Init is included to initialize Status. It is not relevant to this
     --  test.
     with Refined_Post => (Status = EnclaveQuiescent)
   is
   begin
      Status := EnclaveQuiescent;
   end Init;

   procedure CompleteFailedAdminLogon
     --  CompleteFailedAdminLogon has a Global => (Output => Status). For some
     --  reason, keeping the Depends contract causes GNATprove --flow-show-gg
     --  not to create a .gg file.
     --
     --  Remove the Depends contract and the .gg file will be created with the
     --  correct contract: Global => (Output => Status).
     with Depends => (Status => null)
   is
   begin
      Status := EnclaveQuiescent;
   end CompleteFailedAdminLogon;

end Enclave;
