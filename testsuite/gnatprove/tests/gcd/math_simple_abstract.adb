package body Math_Simple_Abstract is

   procedure Lemma_Mult_Then_Div_Is_Ident (Arg1, Arg2 : Positive) with
     Ghost,
     Global => null,
     Post => (Arg1 * Arg2) / Arg2 = Arg1
   is
   begin
      null;
   end Lemma_Mult_Then_Div_Is_Ident;

   procedure Lemma_Mod_Not_Zero (Arg1, Arg2 : Positive) with
     Ghost,
     Global => null,
     Pre  => Arg1 mod Arg2 /= 0,
     Post => not Divides (Arg2, Arg1)
   is
   begin
      for J in Positive loop
         Lemma_Mult_Then_Div_Is_Ident (J, Arg2);
         pragma Assert (Arg2 * J /= Arg1);
         pragma Loop_Invariant (for all K in 1 .. J => Arg2 * K /= Arg1);
      end loop;
   end Lemma_Mod_Not_Zero;

   procedure Lemma_Mod_Zero (Arg1, Arg2 : Positive) with
     Ghost,
     Global => null,
     Pre  => Arg1 mod Arg2 = 0,
     Post => Divides (Arg2, Arg1)
   is
   begin
      null;
   end Lemma_Mod_Zero;

   function GCD (A, B : in Positive) return Positive is
      C : Positive := Integer'Min (A, B);
   begin
      while C > 1 loop
         exit when A mod C = 0 and B mod C = 0;
         if A mod C /= 0 then
            Lemma_Mod_Not_Zero (A, C);
         else
            Lemma_Mod_Not_Zero (B, C);
         end if;
         pragma Loop_Invariant (C > 1 and then
           (for all X in C .. Integer'Min (A, B) => not (Divides (X, A) and Divides (X, B))));
         C := C - 1;
      end loop;

      Lemma_Mod_Zero (A, C);
      Lemma_Mod_Zero (B, C);

      return C;
   end GCD;

end Math_Simple_Abstract;
