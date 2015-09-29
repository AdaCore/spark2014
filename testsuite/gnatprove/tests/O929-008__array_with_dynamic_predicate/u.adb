package body U with SPARK_Mode is

   procedure Loop_Test (Sq : in out Sequence) is
   begin

      for I in 0 .. Sq'Last loop

         Sq(I) := 0;

         pragma Loop_Invariant
           (for all J in I+1 .. Sq'Last =>
              Sq(J) = Sq'Loop_Entry(J));

      end loop;

   end Loop_Test;

end U;
