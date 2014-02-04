with System.Storage_Elements;

package body ProgramSwitch
  with Refined_State => (Inputs => (Inputs_C,
                                    Input_Ext))
is
   Inputs_C : Positions;

   Input_Ext : Positions
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Read (Value : out Positions)
     with Refined_Global  => (Input  => Input_Ext,
                              Output => Inputs_C),
          Refined_Depends => ((Inputs_C,
                               Value) => Input_Ext)
   is
   begin
      Inputs_C := Input_Ext;
      Value    := Inputs_C;
   end Read;

end ProgramSwitch;
