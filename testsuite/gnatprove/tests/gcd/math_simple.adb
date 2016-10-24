package body Math_Simple is

   function GCD (A, B : in Positive) return Positive is
      C : Positive := Integer'Min (A, B);
   begin
      while C > 1 loop
         exit when A mod C = 0 and B mod C = 0;
         pragma Loop_Invariant (for all X in C .. Integer'Min (A, B) =>
                                  not (Divides (X, A) and Divides (X, B)));
         C := C - 1;
      end loop;

      return C;
   end GCD;

end Math_Simple;
