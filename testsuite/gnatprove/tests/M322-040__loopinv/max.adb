package body Max is

   procedure Step (A: in Arr; I : Index; Max: in out Integer) is
   begin
      pragma Assert
        (for all M in Integer =>
           --  if M is the current maximum over 1 .. I, then Max = M
           (if (for all N in Index range 1..I => (A(N) <= M))
                 and
               (for some N in Index range 1..I => (A(N) = M))
            then M = Max));
      pragma Assert
        --  Max is the current maximum over 1 .. I-1
        ((for all N in Index range 1..I-1 => (A(N) <= Max))
           and
         (for some N in Index range 1..I-1 => (A(N) = Max)));
      if A(I) < Max then
         Max := A(I);
      end if;
      pragma Assert
        (for all M in Integer =>
           --  if M is the current maximum over 1 .. I, then Max = M
           (if (for all N in Index range 1..I => (A(N) <= M))
                 and
               (for some N in Index range 1..I => (A(N) = M))
            then M = Max));
   end Step;

   procedure MaxElement_P1B1_A (A: in Arr; Max: out Integer)
   is
   begin
      Max := A(1);
      for I in Index loop
         --  Max is the current maximum over 1 .. I-1
         pragma Assert ((for all N in Index range 1..I-1 => (A(N) <= Max))
                          and
                        (for some N in Index range 1..I-1 => (A(N) = Max)));
         if A(I) < Max then
            Max := A(I);
         end if;
         pragma Loop_Invariant
           (for all M in Integer =>
              --  if M is the current maximum over 1 .. I, then Max = M
              (if (for all N in Index range 1..I => (A(N) <= M))
                    and
                  (for some N in Index range 1..I => (A(N) = M))
               then M = Max));
      end loop;
   end MaxElement_P1B1_A;

end Max;
