with Pack; use Pack; pragma Elaborate (Pack);
procedure Main_Pre
   with Global => Pack.State,
        Pre => Pack.Is_Valid
is
begin
   P;
end Main_Pre;
