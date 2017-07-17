procedure Simple_Loops_Unroll with
  SPARK_Mode
is
   Prop : Boolean;
begin
   Prop := False;
   for J in 1 .. 10 loop

      Prop := True;
   end loop;

   Prop := True;
   for J in 1 .. 10 loop

      Prop := False;
   end loop;

   Prop := True;
   for J in 1 .. 10 loop
      pragma Assert (Prop);
      Prop := Prop;
   end loop;

   Prop := True;
   for J in 1 .. 10 loop
      pragma Assert (if J > 1 then Prop);
      Prop := Prop;
   end loop;

end Simple_Loops_Unroll;
