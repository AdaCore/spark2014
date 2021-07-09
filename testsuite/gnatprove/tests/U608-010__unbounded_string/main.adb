with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

procedure Main is
   U : Unbounded_String;
begin
   pragma Assert (U = Null_Unbounded_String);
end;
