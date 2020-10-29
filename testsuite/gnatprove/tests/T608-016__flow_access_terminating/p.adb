procedure Test (CB : not null access procedure)
  with Annotate => (GNATprove, Terminating)
is
begin
   CB.all;
end;
