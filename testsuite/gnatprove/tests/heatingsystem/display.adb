-- Control Panel Boundary Packages

with System.Storage_Elements;

package body Display is  

   Outputs : Displays;

   Output_Ext : Displays;
   for Output_Ext'Address use System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   function PF_Write return Displays is
      (Outputs);

   procedure Write (Content : in Displays) is
   begin
      Outputs    := Content;
      Output_Ext := Content;
   end Write;

end Display;
