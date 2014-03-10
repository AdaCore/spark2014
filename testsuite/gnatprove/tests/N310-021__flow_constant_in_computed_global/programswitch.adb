with System.Storage_Elements;

package body ProgramSwitch
is
   Input_Ext : Positions
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Read (Value : out Positions)
   is
   begin
      Value := Input_Ext;
   end Read;

end ProgramSwitch;
