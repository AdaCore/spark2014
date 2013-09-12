package ModeSwitch
--# own in Inputs : Modes;
is pragma SPARK_Mode (On);
   type Modes is (off, cont, timed);

   function PF_Read return Modes;

   procedure Read( Value : out Modes)
     with Post => (Value = PF_Read);
   --# global  in Inputs;
   --# derives Value from Inputs;
   --# post (Value = Inputs~); -- simplified postcondition valid for single reads
   --
   -- Reads the position of the mode switch.

end ModeSwitch;
