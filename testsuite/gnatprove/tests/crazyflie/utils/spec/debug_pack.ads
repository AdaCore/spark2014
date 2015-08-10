with Interfaces.C; use Interfaces.C;
with Interfaces.C.Extensions; use Interfaces.C.Extensions;

package Debug_Pack is

   --  Functions and procedures

   procedure Debug_Print (Str : String);

   --  Wrapper for the 'consolePuts' function
   --  declared in 'utils/interface/debug.h'
   function C_ConsolePuts (Str : char_array) return Integer;
   pragma Import (C, C_ConsolePuts, "consolePuts");

   --  Wrapper for the 'consolePutchar' function
   --  declared in 'utils/interface/debug.h'
   function C_ConsolePutchar (Ch : Integer) return Integer;
   pragma Import (C, C_ConsolePutchar, "consolePutchar");

private

   function To_C   (Item : Character) return char;

   function To_C
     (Item       : String;
      Append_Nul : Boolean := True) return char_array;


end Debug_Pack;
