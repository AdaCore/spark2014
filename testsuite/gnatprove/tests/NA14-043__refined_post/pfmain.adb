with PF;
with Sink;

procedure PFMain
with SPARK_Mode
is
   A : Integer := 10;
   B : Integer;
begin
   PF.Test (A, B);
   Sink.The_Sink := B;
end PFMain;
