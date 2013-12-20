package body Review_Test
  with SPARK_Mode,
       Refined_State => (State => (X, Y))
is
   X, Y : Integer := 0;

   procedure Does_Something (A : out Integer)
     with Refined_Global  => (X, Y, Var, Logging.Testpoint),
          Refined_Depends => (A    => (X, Y),
                              null => (Var, Logging.Testpoint))
   is
   begin
      A := X;

      if Var = 0 then
         Logging.Trace1 (X);
         Logging.Trace2;
      end if;

      if Y < 0 then
         Logging.Trace1 (Y);
      else
         A := A + 1;
      end if;
   end Does_Something;
end Review_Test;
