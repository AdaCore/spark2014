with Pack; use Pack; pragma Elaborate (Pack);
procedure MainPre
   with Global => Pack.State,
        Pre => Pack.Is_Valid
is
begin
   P;
end MainPre;
