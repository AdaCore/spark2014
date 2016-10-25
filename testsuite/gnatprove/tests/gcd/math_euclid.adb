package body Math_Euclid is

   procedure Lemma_Divisor_Mod (A, B, X : Positive) with
     Ghost,
     Global => null,
     Pre  => Divides (X, A) and then Divides (X, B) and then not Divides (B, A),
     Post => Divides (X, A mod B)
   is
   begin
      null;
   end Lemma_Divisor_Mod;

   procedure Lemma_Divisor_Transitive (A, B, X : Positive) with
     Ghost,
     Global => null,
     Pre  => Divides (B, A) and then Divides (X, B),
     Post => Divides (X, A)
   is
   begin
      null;
   end Lemma_Divisor_Transitive;

   procedure Lemma_Divisor_Mod_Inverse (A, B, X : Positive) with
     Ghost,
     Global => null,
     Pre  => not Divides (B, A) and then Divides (X, A mod B) and then Divides (X, B),
     Post => Divides (X, A)
   is
   begin
      null;
   end Lemma_Divisor_Mod_Inverse;

   procedure Lemma_Same_Divisor_Mod (A, B : Positive) with
     Ghost,
     Global => null,
     Post => (for all X in Positive =>
                (Divides (X, A) and Divides (X, B))
                  =
                (Divides (X, B) and then (Divides (B, A) or else Divides (X, A mod B))))
   is
   begin
      for X in Positive loop
         if Divides (X, A) and then Divides (X, B) and then not Divides (B, A) then
            Lemma_Divisor_Mod (A, B, X);
         end if;
         if Divides (B, A) and then Divides (X, B) then
            Lemma_Divisor_Transitive (A, B, X);
         end if;
         if not Divides (B, A) and then Divides (X, A mod B) and then Divides (X, B) then
            Lemma_Divisor_Mod_Inverse (A, B, X);
         end if;
         pragma Loop_Invariant
           (for all Y in 1 .. X =>
              (Divides (Y, A) and Divides (Y, B))
                =
              (Divides (Y, B) and then (Divides (B, A) or else Divides (Y, A mod B))));
      end loop;
   end Lemma_Same_Divisor_Mod;

   function GCD (A, B : in Positive) return Positive is
      An : Positive := A;
      Bn : Natural := B;
      C  : Positive;
   begin
      while Bn /= 0 loop
         C  := An;
         An := Bn;
         Bn := C mod Bn;
         Lemma_Same_Divisor_Mod (C, An);
         pragma Loop_Invariant
           (for all X in Positive =>
              (Divides (X, A) and Divides (X, B))
                =
              (Divides (X, An) and (Bn = 0 or else Divides (X, Bn))));
      end loop;

      pragma Assert (Divides (An, An));
      pragma Assert (Divides (An, A));
      pragma Assert (Divides (An, B));

      pragma Assert (for all X in An + 1 .. Integer'Min (A, B) =>
                       not (Divides (X, A) and Divides (X, B)));
      return An;
   end GCD;

end Math_Euclid;
