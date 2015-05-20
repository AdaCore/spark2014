package body Split
  with SPARK_Mode
is
   procedure P is
   begin
      null;
   end P;

   procedure Q is
   begin
      for J in 1 .. 5 loop
         pragma Loop_Invariant (U in 1 .. 20 and then V in 1.. 20);
         P;
      end loop;
   end Q;

end Split;
