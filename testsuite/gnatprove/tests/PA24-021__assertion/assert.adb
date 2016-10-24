procedure Assert (X, Y : Integer)
  with SPARK_Mode
is
begin
   if X < Y or X > Y then
      return;
   end if;
   pragma Assert (X = Y);
end Assert;
