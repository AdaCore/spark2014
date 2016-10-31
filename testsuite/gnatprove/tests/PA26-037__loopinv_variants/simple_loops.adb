procedure Simple_Loops with
  SPARK_Mode
is
   Prop : Boolean;
begin
   for I in 1 .. 3 loop
      Prop := False;
      for J in 1 .. 10 loop
         pragma Loop_Invariant (Prop);  --  @LOOP_INVARIANT_INIT:FAIL @LOOP_INVARIANT_PRESERV:PASS
         Prop := True;
      end loop;
      pragma Loop_Invariant (True);
   end loop;

   for I in 1 .. 3 loop
      Prop := True;
      for J in 1 .. 10 loop
         pragma Loop_Invariant (Prop);  --  @LOOP_INVARIANT_INIT:PASS @LOOP_INVARIANT_PRESERV:FAIL
         Prop := False;
      end loop;
      pragma Loop_Invariant (True);
   end loop;

   for I in 1 .. 3 loop
      Prop := True;
      for J in 1 .. 10 loop
         pragma Loop_Invariant (Prop);  --  @LOOP_INVARIANT_INIT:PASS @LOOP_INVARIANT_PRESERV:PASS
         Prop := Prop;
      end loop;
      pragma Loop_Invariant (True);
   end loop;

   for I in 1 .. 3 loop
      Prop := True;
      for J in 1 .. 10 loop
         pragma Loop_Invariant (if J > 1 then Prop);  --  @LOOP_INVARIANT_INIT:PASS @LOOP_INVARIANT_PRESERV:FAIL
         Prop := Prop;
      end loop;
      pragma Loop_Invariant (True);
   end loop;

end Simple_Loops;
