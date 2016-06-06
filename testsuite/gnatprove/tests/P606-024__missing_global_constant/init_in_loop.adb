procedure Init_In_Loop with SPARK_Mode is
   J : Natural := 1;
begin
   for I in 1 .. 100 loop
      declare
         Fst : constant Natural := (if I < 1 then 0 else 51);
         Lst : constant Natural := (if I > 1 then 100 else 50);
         subtype T is Natural range Fst .. Lst;
         C   : T;
      begin
         pragma Assert (Fst <= Lst); --@ASSERT:FAIL
      end;
      pragma Loop_Invariant (I = J);
      J := J + 1;
   end loop;
end Init_In_Loop;
