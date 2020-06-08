with Ada.Unchecked_Conversion;

package body gnatBug is

   procedure P (X : T) is
      Y : Integer;

      function Conv is new Ada.Unchecked_Conversion
        (Source => T, Target => Integer);

   begin
      Y := Conv (X);
   end;

end;
