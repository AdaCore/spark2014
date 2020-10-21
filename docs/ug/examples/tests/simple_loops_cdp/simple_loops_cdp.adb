procedure Simple_Loops_Cdp with
  SPARK_Mode
is
   Prop : Boolean;
begin
   Prop := False;
   for J in 1 .. 10 loop
      pragma Loop_Invariant (Prop);
      Prop := True;
   end loop;

   Prop := True;
   for J in 1 .. 10 loop
      pragma Loop_Invariant (Prop);
      Prop := False;
   end loop;

   Prop := True;
   for J in 1 .. 10 loop
      pragma Loop_Invariant (Prop);
      Prop := Prop;
   end loop;

   Prop := True;
   for J in 1 .. 10 loop
      pragma Loop_Invariant (if J > 1 then Prop);
      Prop := Prop;
   end loop;

end Simple_Loops_Cdp;
