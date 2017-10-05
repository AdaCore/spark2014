pragma Style_Checks (Off);

package Libxhcidbg_Component.Memory
is

   Xhci_Dma_Address    : constant := 16#0100_0000#;
   Xhci_Dma_Size       : constant := 16#0004_1000#;
   Xhci_Dma_Executable : constant Boolean := False;
   Xhci_Dma_Writable   : constant Boolean := True;

end Libxhcidbg_Component.Memory;
