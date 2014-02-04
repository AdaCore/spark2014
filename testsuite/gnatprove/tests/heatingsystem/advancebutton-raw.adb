with System.Storage_Elements;

-- Raw Advance Button Boundary Package
-- boundary package providing raw access to the advance switch
package body AdvanceButton.Raw
  with Refined_State => (Inputs => (Inputs_C,
                                    Input_Ext))
is
   Inputs_C : Boolean;

   Input_Ext : Boolean
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Read (Pressed : out Boolean)
     with Refined_Global  => (Input  => Input_Ext,
                              Output => Inputs_C),
          Refined_Depends => ((Pressed,
                               Inputs_C) => Input_Ext)
   is
   begin
      Inputs_C := Input_Ext;
      Pressed  := Inputs_C;
   end Read;

end AdvanceButton.Raw;
