private package BSP.PCI_Express.DI2_Buffer
   with Abstract_State => (State with Part_Of => BSP.PCI_Express.Platform_Buffer)
is

   procedure Initialise
     with Global => (Output => State);

end BSP.PCI_Express.DI2_Buffer;
