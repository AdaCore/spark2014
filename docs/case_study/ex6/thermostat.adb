-- Software Engineering with SPARK --
-- Design and Implementation Exercise --
-- Sample Answer (SPARK 95) --

-- Modified as a demonstration of formal verification.  Support for proof of the normal operation of the
-- heating system (as embodied in procedure CheckModeSwitch) has been added.  The routines for programming
-- the heating system (embodied in procedure CheckProgramSwitch) can be proved free from run-time errors
-- but have not been annotated for partial correctness proofs.

-- Boundary (Interface) Packages
-- Thermostat

  with System.Storage_Elements;

  package body Thermostat is

     Inputs : Boolean;

     Input_Ext : Boolean;
     for Input_Ext'Address use System.Storage_Elements.To_Address (16#FFFF_FFFF#);

     -- proof function.  Provides a better name and some abstraction to read of the room thermostat
     function RoomTooWarm return Boolean is
        (Inputs);

     procedure AboveTemp (Result : out Boolean) is
     begin
        Inputs := Input_Ext;
        Result := Inputs;
     end AboveTemp;

     -- Above is is simplified post condition valid for one read of the thermostat.
     -- In SPARK, volatile inputs from outside the program are modelled as infinite sequences of values.
     -- Reading the input takes the first value from the sequence and performs a 'tail operation on the
     -- stream to remove it and leave the next value ready to be read in.  The simplified model, which is
     -- adequate for our purposes ignores the 'tail side effect on the input sequence.

     -- Note the "~" suffix, which means "original value on entry to the subprogram" .

     --
     -- Result is True if the room temperature is above the
     -- required temperature and False otherwise.
  end Thermostat;
