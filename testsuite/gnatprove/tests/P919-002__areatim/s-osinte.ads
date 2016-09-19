pragma Restrictions (No_Elaboration_Code);
--  This could use a comment, why is it here???

with System.BB.MCU_Parameters;

package System.OS_Interface is
   pragma Preelaborate;

   Ticks_Per_Second : constant := 0;
   --  Number of clock ticks per second


end System.OS_Interface;
