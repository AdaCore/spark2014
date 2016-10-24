procedure Div (X, Y : Integer; Res : out Integer)
  with SPARK_Mode
is
begin
   if Y > 0 then
      Res := X / Y;
   end if;
end Div;
