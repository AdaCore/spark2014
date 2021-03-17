procedure Call (X : Integer; Y : out Integer)
  with Depends => (Y => X)
is
   Z : Integer with Address => Y'Address, Import;
   procedure Copy (From : Integer; To : out Integer)
     with Pre => True
   is
   begin
      To := From;
   end;
begin
   Copy (From => X, To => Z);
end;
