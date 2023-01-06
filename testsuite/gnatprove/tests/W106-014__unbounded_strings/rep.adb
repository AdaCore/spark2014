with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Comm; use Comm;
procedure Rep
     (compositionString: Unbounded_String)
 with SPARK_Mode
is
   package Unb renames Comm.Unbounded_Strings_Subprograms;
   position : Natural := Unb.Index (compositionString, "p");
   positionAfterId : Natural;
   positionSpace   : constant Natural :=
     Unb.Index (compositionString, " ", position);
begin
   null;
end Rep;
