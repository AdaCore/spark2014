procedure P (X1, X2 : Integer; Y1, Y2 : out Integer) with
   Depends => (Y1 => X1, Y2 => X2),
   Post => Y1 = X1 and Y2 = X2       --@POSTCONDITION:PASS
is
   type T (D1, D2 : Integer) is record
      C1 : Integer := D1;
      C2 : Integer := D2;
   end record;
begin
   Y1 := T'(D1 => X1, D2 => X2, others => <>).C1;
   Y2 := T'(D1 => X1, D2 => X2, others => <>).C2;
end P;
