procedure Test (CB : not null access procedure)
  with Always_Terminates
is
begin
   CB.all;
end;
