function Add (X, Y : Integer) return Integer
  with SPARK_Mode
is
begin
   --  Dummy unit that contains at least 1 VC
   return X + Y;
end;
