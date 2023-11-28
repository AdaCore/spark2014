procedure Repro (X : Integer)
  with SPARK_Mode, Always_Terminates => True
is
    procedure OS_Exit
    with No_Return, Import, Global => null;
begin
   if X > 0 then
      OS_Exit;
   end if;
end;
