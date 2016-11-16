--  this with cause the below pragma warnings to not work
with Ada.Strings.Fixed;

package body Bar is

   procedure Str (Wibble : in out T)  --  this also needs to be wrong
   with Global => null
   is
      pragma Warnings (Off, "statement has no effect");
      Wobble : T := Wibble;
   begin
      Fnark (Wobble);
   end Str;

end Bar;
