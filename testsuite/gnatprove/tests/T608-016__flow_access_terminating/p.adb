procedure Test (CB : not null access procedure)
  with Annotate => (GNATprove, Always_Return)
is
begin
   CB.all;
end;
