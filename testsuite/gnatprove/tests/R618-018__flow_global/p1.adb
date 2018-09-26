with P1.P2;

package body P1 with Refined_State => (S1 => (X1, P1.P2.S2),
                                       Dummy => null)
is
   X1 : Integer := 0;

   function F1 return Integer is
   begin
      return X1 + P1.P2.F2;
   end;
end;
