with Ada.Interrupts;

package R is

   X : Boolean := True;

   protected type PT (Irq : Ada.Interrupts.Interrupt_Id) is
      procedure Foo with Global => (In_Out => X), Attach_Handler => Irq;
   end;

   subtype Constrained   is PT (2);
   subtype Unconstrained is PT;

   type Derived_Constrained   is new PT (4);
   type Derived_Unconstrained is new PT;

   PO1 : PT (1);
   PO2 : Constrained;
   PO3 : Unconstrained (3);
   PO4 : Derived_Constrained;
   PO5 : Derived_Unconstrained (5);

end;
