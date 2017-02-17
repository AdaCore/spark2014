package body Search is
   pragma Annotate (Formal_Proof, On);
   function Search (T : A; V : Integer) return Integer is
      Pos : Integer := 0;
   begin
      for I in 1 .. 10 loop
         pragma Loop_Invariant
           (for all J in Position range T'First .. I-1 => (T(J) /= V));
         if T (I) = V then
            Pos := I;
            exit;
         end if;
      end loop;
      return Pos;
   end Search;
end Search;
