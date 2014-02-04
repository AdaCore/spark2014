with System.Storage_Elements;

package body Actuator
  with Refined_State => (Outputs => (Outputs_C,
                                     Output_Ext))
is
   -- We don't know anything about how type Settings is implemented but we do
   -- need a type declaration for it so that we can declarae proof functions
   -- that use it. The following proof type declaration does what we need.
   --# type Settings is abstract;

   type Settings is new Boolean;
   Outputs_C : Settings;

   Output_Ext : Settings
     with Volatile,
          Async_Readers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   -- and allows us to define this proof function
   function IsOn return Boolean is (Outputs_C = True)
     with Refined_Global => Outputs_C;

   procedure TurnOn
     with Refined_Global  => (Output => (Outputs_C,
                                         Output_Ext)),
          Refined_Depends => ((Outputs_C,
                               Output_Ext) => null)
   is
   begin
      Outputs_C  := True;
      Output_Ext := True;
   end TurnOn;

   procedure TurnOff
     with Refined_Global  => (Output => (Outputs_C,
                                         Output_Ext)),
          Refined_Depends => ((Outputs_C,
                               Output_Ext) => null)
   is
   begin
      Outputs_C  := False;
      Output_Ext := False;
   end TurnOff;

end Actuator;
