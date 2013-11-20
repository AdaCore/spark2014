package body MaxAndSum is pragma SPARK_Mode (On);

   procedure MaxAndSum (A : ElementArray; Sum : out Natural; Max : out Element)
   is
   begin
      Sum := 0;
      Max := 0;
      for I in 1 .. N loop
         pragma Loop_Invariant (Sum <= (I-1)*Max);
         Sum := Sum + A (I);
         if Max < A (I) then
            Max := A (I);
         end if;
         pragma Assert (Sum <= I*Max);
      end loop;
   end MaxAndSum;

end MaxAndSum;
