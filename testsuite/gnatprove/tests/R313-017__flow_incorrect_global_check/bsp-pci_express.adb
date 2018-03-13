with BSP.PCI_Express.DI2_Buffer;
with BSP.PCI_Express.PS;

package body BSP.PCI_Express
   with Refined_State => (State => BSP.PCI_Express.PS.State,
                          Platform_Buffer => BSP.PCI_Express.DI2_Buffer.State)
is

end BSP.PCI_Express;
