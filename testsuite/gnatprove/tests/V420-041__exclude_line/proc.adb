procedure Proc (B : Boolean; X, Y : in out Integer) with
  Post => X = 42
is
begin
   X := 42;
   if B then
      Y := 5;
   end if;
end Proc;
