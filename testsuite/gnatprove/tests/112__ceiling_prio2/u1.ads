package U1 is

   procedure P1;
   --  Public procedure. Not inlined.

   procedure PAA;
   --  Public procedure. Not inlined.

private
   procedure P2;
   --  Private procedure without a contract. Likely to be inlined.

end U1;
