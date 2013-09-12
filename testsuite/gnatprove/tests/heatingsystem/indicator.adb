with System.Storage_Elements;

package body Indicator is  
   --# type Settings is abstract;

   type Settings is new Boolean;
   Outputs : Settings;

   Output_Ext : Settings;
   for Output_Ext'Address use System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   -- and allows us to define this proof function
   function IsOn return Boolean is
      (Outputs = True);

   procedure TurnOn is
   begin
      Outputs    := True;
      Output_Ext := True;
   end TurnOn;

   procedure TurnOff is
   begin
      Outputs    := False;
      Output_Ext := False;
   end TurnOff;

end Indicator;
