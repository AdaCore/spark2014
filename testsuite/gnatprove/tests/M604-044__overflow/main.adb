with Test; use Test;

procedure Main
is
   Tmp : Enum_T := Elem_2;
begin
   Tmp := Range_Check_Error (Tmp);
end Main;
