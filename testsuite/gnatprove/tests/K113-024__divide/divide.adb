package body Divide is
   procedure Divide (M, N : in Integer; Q, R: out Integer)
   is
   begin
      Q := 0;
      R := M;
      while R >= N loop
         pragma Loop_Invariant (Q <= M - R
                                  and then M = Q * N + R
                                  and then R >= 0);
         Q := Q + 1;
         R := R - N;
      end loop;
   end Divide;
end Divide;
