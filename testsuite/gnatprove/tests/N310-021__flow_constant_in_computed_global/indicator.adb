with System.Storage_Elements;

package body Indicator
is
   type Settings is new Boolean;

   Output_Ext : Settings
     with Volatile,
          Async_Readers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure TurnOn
   is
   begin
      Output_Ext := True;
   end TurnOn;

   procedure TurnOff
   is
   begin
      Output_Ext := False;
   end TurnOff;

end Indicator;
