procedure U2 (X1, X2 : Integer; Y1, Y2 : out Integer)
  with SPARK_Mode,
       Depends => (Y1 => X1, Y2 => X2),
       Post => Y1 = X1 and Y2 = X2
is
   type R is record
      C1, C2 : Integer;
   end record;

   Before : constant R := (C1 => 0, C2 => 0);
begin
   Y1 := Before'Update (C1 => X1, C2 => X2).C1;
   Y2 := Before'Update (C1 => X1, C2 => X2).C2;
end;
