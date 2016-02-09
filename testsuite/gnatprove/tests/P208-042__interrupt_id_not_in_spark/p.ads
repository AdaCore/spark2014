with Ada.Interrupts;

package P is

   Bad_Interrupt_ID     : aliased Ada.Interrupts.Interrupt_ID;

   Bad_Interrupt_ID_Ptr : access Ada.Interrupts.Interrupt_ID := Bad_Interrupt_ID'Access;

end;
