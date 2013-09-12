with System.Storage_Elements;

package body Actuator is  
   -- We don't know anything about how type Settings is implemented but we do need a type
   -- declaration for it so that we can declarae proof functions that use it.  The following
   -- proof type declaration does what we need.
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

end Actuator;
