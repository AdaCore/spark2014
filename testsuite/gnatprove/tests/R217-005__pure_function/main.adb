with P;
pragma Elaborate (P);

procedure Main
  with Pre => P.X
is
begin
   pragma Assert (P.Get);
   P.Reset;
   pragma Assert (not P.Get);
end;
