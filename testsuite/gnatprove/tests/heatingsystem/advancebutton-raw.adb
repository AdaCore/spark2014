with System.Storage_Elements;

-- Raw Advance Button Boundary Package
-- boundary package providing raw access to the advance switch
package body AdvanceButton.Raw is  

   Inputs : Boolean;

   Input_Ext : Boolean;
   for Input_Ext'Address use System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Read (Pressed : out Boolean) is
   begin
      Inputs  := Input_Ext;
      Pressed := Inputs;
   end Read;

end AdvanceButton.Raw;
