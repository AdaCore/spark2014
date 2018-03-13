package body BSP.PCI_Express.PS
   with Refined_State => (State => X)
is
   X  : Boolean;


   procedure Foo
      with Global => (In_Out => (X,
                                 BSP.PCI_Express.Platform_Buffer))
   is
   begin
      if X then
         X := False;
      end if;
   end Foo;


end BSP.PCI_Express.PS;
