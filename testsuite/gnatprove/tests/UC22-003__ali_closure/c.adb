with B;
procedure C with SPARK_Mode is
begin
   B.Set;
   B.P;
   pragma Assert (B.Valid);
end C;
