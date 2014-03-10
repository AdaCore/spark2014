with System.Storage_Elements;

-- Raw Advance Button Boundary Package
-- boundary package providing raw access to the advance switch
package body AdvanceButton.Raw
is
   Input_Ext : Boolean
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Read (Pressed : out Boolean)
   is
   begin
      Pressed  := Input_Ext;
   end Read;

end AdvanceButton.Raw;
