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
   -- proof function. Provides a better name and some abstraction to read of
   -- the room thermostat
   function RoomTooWarm return Boolean
     with Global => Inputs;

   procedure AboveTemp (Result : out Boolean)
     with Global  => (In_Out => Inputs),
          Depends => ((Inputs,
                       Result) => Inputs),
          Post    => Result = RoomTooWarm;
end Thermostat;
