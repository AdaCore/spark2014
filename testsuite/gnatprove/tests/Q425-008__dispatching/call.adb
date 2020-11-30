with Parent; use Parent;
with Child; use Child;

procedure Call with SPARK_Mode is
   V : T'Class := Get;
begin
   V.P;
end Call;
