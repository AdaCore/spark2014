package body P is

   procedure Init (X : out A) is
   begin
      --  SPARK 2005 example uses accept annotation here:
      --  corresponding syntax is TBD.
      for I in Positive range X'First .. X'Last loop
         X (I) := 0;
         pragma Loop_Invariant (for all J in Positive range X'First .. I => (X (J) = 0));
      end loop;
   end Init;

end P;
