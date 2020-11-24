procedure T (X1, X2 : Integer; Y1, Y2 : out Integer)
  with SPARK_Mode,
       Depends => (Y1 => X1, Y2 => X2),
       Post => Y1 = X1 and Y2 = X2
is
   type R is record
      C1, C2 : Integer;
   end record;

begin
   Y1 := R'(C1 => X1, C2 => X2).C1;
   Y2 := R'(C1 => X1, C2 => X2).C2;
end;
