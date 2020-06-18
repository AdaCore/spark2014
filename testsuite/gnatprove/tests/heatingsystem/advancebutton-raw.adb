with System.Storage_Elements;

-- Raw Advance Button Boundary Package
-- boundary package providing raw access to the advance switch
package body AdvanceButton.Raw
  with Refined_State => (Inputs => Input_Ext)
is
   Input_Ext : Boolean
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);
   pragma Annotate(Gnatprove, Intentional, "constraints on bit representation","");

   procedure Read (Pressed : out Boolean)
     with Refined_Global  => Input_Ext,
          Refined_Depends => (Pressed => Input_Ext)
   is
   begin
      Pressed  := Input_Ext;
   end Read;

end AdvanceButton.Raw;
