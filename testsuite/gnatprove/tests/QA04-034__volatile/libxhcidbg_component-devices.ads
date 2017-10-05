pragma Style_Checks (Off);

package Libxhcidbg_Component.Devices
is

   Xhci_Xhci_Registers_Address    : constant := 16#e000_0000#;
   Xhci_Xhci_Registers_Size       : constant := 16#0001_0000#;
   Xhci_Xhci_Registers_Executable : constant Boolean := False;
   Xhci_Xhci_Registers_Writable   : constant Boolean := True;

end Libxhcidbg_Component.Devices;
