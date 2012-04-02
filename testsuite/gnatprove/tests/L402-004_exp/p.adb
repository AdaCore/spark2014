procedure P (X : in out Integer; Y : in out Float) is
begin
   if abs X < 1000 and then abs Y < 1000.0 then
      X := X ** 2;
      Y := Y ** 2;
   elsif X ** 2 > 0 then
      X := X ** 2;
      Y := Y ** 2;
   end if;
end P;
