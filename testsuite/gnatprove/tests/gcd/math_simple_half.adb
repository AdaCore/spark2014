package body Math_Simple_Half is

   procedure Lemma_Not_Divisor (Arg1, Arg2 : Positive) with
     Ghost,
     Global => null,
     Pre  => Arg1 in Arg2 / 2 + 1 .. Arg2 - 1,
     Post => not Divides (Arg1, Arg2)
   is
   begin
      null;
   end Lemma_Not_Divisor;

   function GCD (A, B : in Positive) return Positive is
      C : Positive;
   begin
      if A = B then
         return A;

      elsif A = 1 or B = 1 then
         return 1;

      elsif Divides (A, B) then
         return A;

      elsif Divides (B, A) then
         return B;

      else
         C := Integer'Min (A, B) / 2;
         for J in C + 1 .. Integer'Min (A, B) - 1 loop
            Lemma_Not_Divisor (J, Integer'Min (A, B));
            pragma Loop_Invariant (for all X in C + 1 .. J =>
                                     not Divides (X, Integer'Min (A, B)));
         end loop;

         while C > 1 loop
            exit when A mod C = 0 and B mod C = 0;
            pragma Loop_Invariant (C > 1);
            pragma Loop_Invariant (for all X in C .. Integer'Min (A, B) =>
                                     not (Divides (X, A) and Divides (X, B)));
            C := C - 1;
         end loop;

         return C;
      end if;
   end GCD;

end Math_Simple_Half;
