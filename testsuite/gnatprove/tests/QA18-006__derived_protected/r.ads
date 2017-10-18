package R is

   protected type PT (Irq : Integer) is
   end;

   type Derived_Constrained is new PT (1);

end;
