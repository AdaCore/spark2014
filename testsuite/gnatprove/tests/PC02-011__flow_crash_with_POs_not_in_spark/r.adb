with P;
procedure R with SPARK_Mode => On is
   Res : Integer;
begin
   Res := P.PO.Fun;
end R;
