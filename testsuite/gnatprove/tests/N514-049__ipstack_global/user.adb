with Inter; use Inter;

procedure User (X : out Boolean) with
  Global => null
is
begin
   X := Call_Get;
end User;

