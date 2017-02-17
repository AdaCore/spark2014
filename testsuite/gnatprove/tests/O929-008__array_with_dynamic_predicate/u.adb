package body U with SPARK_Mode is

   procedure Loop_Test (Sq : in out Sequence) is
   begin

      for I in 0 .. Sq'Last loop

         pragma Loop_Invariant
           (for all J in I .. Sq'Last =>
              Sq(J) = Sq'Loop_Entry(J));

         Sq(I) := 0;

      end loop;

   end Loop_Test;

end U;
