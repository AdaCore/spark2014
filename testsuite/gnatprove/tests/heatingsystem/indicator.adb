with System.Storage_Elements;

package body Indicator
  with Refined_State => (Outputs => Output_Ext)
is
   type Settings is new Boolean;

   Output_Ext : Settings
     with Volatile,
          Async_Readers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);
   pragma Annotate(Gnatprove, Intentional, "constraints on bit representation","");

   procedure TurnOn
     with Refined_Global  => (Output => Output_Ext),
          Refined_Depends => (Output_Ext => null)
   is
   begin
      Output_Ext := True;
   end TurnOn;

   procedure TurnOff
     with Refined_Global  => (Output => Output_Ext),
          Refined_Depends => (Output_Ext => null)
   is
   begin
      Output_Ext := False;
   end TurnOff;

end Indicator;
