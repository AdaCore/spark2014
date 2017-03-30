--  Implements the instructions available in sdc.

package Instructions
with SPARK_Mode => On
is

   type Instruction is (Clear, Print, Quit);
   --  The actual instruction type.

   function Read (Word : String) return Instruction;
   --  If Word contains the name of a valid instruction the instruction is
   --  returned, otherwise Except.User_Error is raised.

   procedure Process (I : Instruction);
   --  Processes an Instruction.

end Instructions;


