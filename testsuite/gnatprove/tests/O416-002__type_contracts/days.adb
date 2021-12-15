package body Days
  with SPARK_Mode
is
   procedure Next (D : in out Day) is
   begin
      if D = Sunday then
         D := Monday;
      else
         D := Day'Succ (D);
      end if;
   end Next;

   procedure Next_T (D : in out T_Day) is
      Tmp : Day := D;
   begin
      Next (Tmp);
      while Tmp not in T_Day loop
         Next (Tmp);
      end loop;
      D := Tmp;
   end Next_T;

end Days;
