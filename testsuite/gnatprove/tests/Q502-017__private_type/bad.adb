with P1; use P1;
with P2; use P2;
procedure Bad (X : T1; Y : T2) with SPARK_Mode is
begin
   pragma Assert (Always_True (X, X));
   pragma Assert (Always_True (Y, Y));
   pragma Assert (False); --@ASSERT:FAIL
end Bad;
