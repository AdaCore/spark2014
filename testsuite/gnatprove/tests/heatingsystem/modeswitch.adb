with System.Storage_Elements;

package body ModeSwitch
  with Refined_State => (Inputs => Input_Ext)
is
   Input_Ext : Modes
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Read (Value : out Modes)
     with Refined_Global  => Input_Ext,
          Refined_Depends => (Value => Input_Ext)
   is
   begin
      Value := Input_Ext;
   end Read;

end ModeSwitch;
