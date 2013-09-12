package body Search is

   function Search (T : A; V : Integer) return Integer is
      Pos : Integer := 0;
   begin
      for I in 1 .. 10 loop
	 --  Possible run-time errors below due to non-lazy operators used
         pragma Loop_Invariant
           ((Pos = 0 and then
	       (for all J in Position range T'First .. I-1 => (T(J) /= V)))
	    or else
	      (T(Pos) = V and then
		 (for all J in Position range T'First .. Pos-1 => (T(J) /= V))));
         if T (I) = V then
            Pos := I;
            --  exit;
         end if;
      end loop;
      return Pos;
   end Search;
end Search;
