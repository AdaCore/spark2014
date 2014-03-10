with System.Storage_Elements;

-- Control Panel Boundary Packages
package body Display
is
   Output_Ext : Displays
     with Volatile,
          Async_Readers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Write (Content : in Displays)
   is
   begin
      Output_Ext := Content;
   end Write;

end Display;
