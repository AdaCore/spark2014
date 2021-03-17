procedure Assign (X : Integer; Y : out Integer)
  with Depends => (Y => X)
is
   Z : Integer with Address => Y'Address, Import;
begin
   Z := X;
end;
