with Connection; use Connection;
with Use_Connection; use Use_Connection;

procedure Proc
  with SPARK_Mode
is
   P : IO_Pulse_T;

begin
   Init_Null (P);
   pragma Assert (Is_Detached (P.Coid));  --  @ASSERT:PASS @INIT_BY_PROOF:PASS

   Init (P);
   pragma Assert (Is_Detached (P.Coid));  --  @ASSERT:FAIL @INIT_BY_PROOF:FAIL

end Proc;
