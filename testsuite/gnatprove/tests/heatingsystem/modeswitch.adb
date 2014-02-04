with System.Storage_Elements;

package body ModeSwitch
  with Refined_State => (Inputs => (Inputs_C,
                                    Input_Ext))
is
   Inputs_C : Modes;

   Input_Ext : Modes
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   function PF_Read return Modes is (Inputs_C)
     with Refined_Global => Inputs_C;

   procedure Read (Value : out Modes)
     with Refined_Global  => (Input  => Input_Ext,
                              Output => Inputs_C),
          Refined_Depends => ((Inputs_C,
                               Value) => Input_Ext)
   is
   begin
      Inputs_C := Input_Ext;
      Value    := Inputs_C;
   end Read;

end ModeSwitch;
