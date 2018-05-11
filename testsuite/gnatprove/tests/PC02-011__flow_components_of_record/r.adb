with P;
procedure R with SPARK_Mode => On is
   Res : Integer;
begin
   Res := P.Ob.B.F;
end R;
