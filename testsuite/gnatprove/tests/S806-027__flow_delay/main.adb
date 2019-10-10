with P;

procedure Main is
begin
   P.Dummy; --  this call will read P.X without initializing it
end;
