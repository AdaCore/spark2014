with P;

procedure Main
   with Global => (In_Out => P.State)
is
begin
   P.Hidden;
end;
