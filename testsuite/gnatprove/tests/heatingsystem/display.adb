with System.Storage_Elements;

-- Control Panel Boundary Packages
package body Display
  with Refined_State => (Outputs => Output_Ext)
is
   Output_Ext : Displays
     with Volatile,
          Async_Readers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);
   pragma Annotate(Gnatprove, Intentional, "constraints on bit representation","");

   procedure Write (Content : in Displays)
     with Refined_Global  => (Output => Output_Ext),
          Refined_Depends => (Output_Ext => Content)
   is
   begin
      Output_Ext := Content;
   end Write;

end Display;
