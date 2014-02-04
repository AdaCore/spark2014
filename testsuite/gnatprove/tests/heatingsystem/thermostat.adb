-- Software Engineering with SPARK --
-- Design and Implementation Exercise --
-- Sample Answer (SPARK 2014) --

-- Modified as a demonstration of formal verification.  Support for proof of
-- the normal operation of the heating system (as embodied in procedure
-- CheckModeSwitch) has been added. The routines for programming the heating
-- system (embodied in procedure CheckProgramSwitch) can be proved free from
-- run-time errors but have not been annotated for partial correctness proofs.

-- Boundary (Interface) Packages
-- Thermostat
with System.Storage_Elements;

package body Thermostat
  with Refined_State => (Inputs => (Inputs_C,
                                    Input_Ext))
is
   Inputs_C : Boolean;

   Input_Ext : Boolean
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   -- proof function. Provides a better name and some abstraction to read of
   -- the room thermostat
   function RoomTooWarm return Boolean is (Inputs_C)
     with Refined_Global => Inputs_C;

   procedure AboveTemp (Result : out Boolean)
     with Refined_Global  => (Input  => Input_Ext,
                              Output => Inputs_C),
          Refined_Depends => ((Inputs_C,
                               Result) => Input_Ext)
   is
   begin
      Inputs_C := Input_Ext;
      Result   := Inputs_C;
   end AboveTemp;
end Thermostat;
