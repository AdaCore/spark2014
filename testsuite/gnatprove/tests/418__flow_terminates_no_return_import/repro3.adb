with P;

procedure Repro3 (X : Integer)
  with SPARK_Mode, Always_Terminates => True
is
    procedure Trap
    with No_Return, Global => (In_Out => P.G);
    pragma Import (Intrinsic, Trap, "__builtin_trap");
begin
   if X > 0 then
      Trap;
   end if;
end;
