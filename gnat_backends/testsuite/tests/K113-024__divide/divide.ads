package Divide is
   procedure Divide (M, N : in Integer; Q, R: out Integer)
      with Pre => (M >= 0 and then N > 0),
           Post => (M = Q * N + R and then R < N and then R >= 0);
end Divide;
