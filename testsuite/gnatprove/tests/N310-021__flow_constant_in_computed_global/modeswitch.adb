with System.Storage_Elements;

package body ModeSwitch
is
   Input_Ext : Modes
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Read (Value : out Modes)
   is
   begin
      Value := Input_Ext;
   end Read;

end ModeSwitch;
