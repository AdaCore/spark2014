with System.Storage_Elements;

package body ProgramSwitch
  with Refined_State => (Inputs => Input_Ext)
is
   Input_Ext : Positions
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Read (Value : out Positions)
     with Refined_Global  => Input_Ext,
          Refined_Depends => (Value => Input_Ext)
   is
   begin
      Value := Input_Ext;
   end Read;

end ProgramSwitch;
