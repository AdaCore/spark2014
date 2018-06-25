with P;
procedure Main with SPARK_Mode is
begin
   pragma Assert (P.F1);
   pragma Assert (P.F2);
   pragma Assert (P.F3);
end;
