-- Software Engineering with SPARK --
-- Design and Implementation Exercise --
-- Sample Answer (SPARK 2014) --

-- Modified as a demonstration of formal verification. Support for proof of the
-- normal operation of the heating system (as embodied in procedure
-- CheckModeSwitch) has been added.  The routines for programming the heating
-- system (embodied in procedure CheckProgramSwitch) can be proved free from
-- run-time errors but have not been annotated for partial correctness proofs.

-- Boundary (Interface) Packages
-- Thermostat
package Thermostat
  with Abstract_State => (Inputs with External => Async_Writers)
is
   procedure AboveTemp (Result : out Boolean)
     with Global  => Inputs,
          Depends => (Result => Inputs);
end Thermostat;
