with System;

package body Debug_Pack is

   function C_ConsolePuts (Str : System.Address) return Integer;
   pragma Import (C, C_ConsolePuts, "consolePuts");
   --  Binding for the 'consolePuts' function
   --  declared in 'utils/interface/debug.h'

   procedure Debug_Print (Str : String) is
      Ignore : Integer;
      Buffer : aliased String (1 .. Str'Length + 1);
   begin
      Buffer (1 .. Str'Length) := Str;
      Buffer (Buffer'Last) := ASCII.NUL;
      Ignore := C_ConsolePuts (Buffer'Address);
   end Debug_Print;

end Debug_Pack;
