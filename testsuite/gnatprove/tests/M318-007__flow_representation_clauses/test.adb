with System.Storage_Elements;

package body Test is 
   procedure Edit (X : out Integer)
   is
      Temp : Integer;
      for Temp'Address use System.Storage_Elements.To_Address(16#DEAD_BEEF#);
   begin
      X := Temp;
   end Edit;
end Test;
