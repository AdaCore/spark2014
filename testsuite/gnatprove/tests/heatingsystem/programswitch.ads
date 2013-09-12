package ProgramSwitch
--# own in Inputs;
is pragma SPARK_Mode (On);

   type Positions is (auto, clock, on1, off1, on2, off2);

   procedure Read( Value : out Positions);
   --# global  in Inputs;
   --# derives Value from Inputs;
   --
   -- Reads the position of the program switch.

end ProgramSwitch;
