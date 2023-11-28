with P;

procedure Repro2 (X : Integer)
  with SPARK_Mode, Always_Terminates => True
is
    procedure OS_Exit
    with No_Return, Import, Global => (In_Out => P.G);
begin
   if X > 0 then
      OS_Exit;
   end if;
end;
