with System.Storage_Elements;

-- Control Panel Boundary Packages
package body Display
  with Refined_State => (Outputs => (Outputs_C,
                                     Output_Ext))
is

   Outputs_C : Displays;

   Output_Ext : Displays
     with Volatile,
          Async_Readers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   function PF_Write return Displays is (Outputs_C)
     with Refined_Global => Outputs_C;

   procedure Write (Content : in Displays)
     with Refined_Global  => (Output => (Output_Ext,
                                         Outputs_C)),
          Refined_Depends => ((Outputs_C,
                               Output_Ext) => Content)
   is
   begin
      Outputs_C  := Content;
      Output_Ext := Content;
   end Write;

end Display;
