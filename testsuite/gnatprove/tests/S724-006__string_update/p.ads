package P with Initializes => X is
   X : Integer := 0;

   procedure Nop1 (S : in out String)
   with Post => S(S'First .. 1)'Old'Update (X => 'X') = "123",
        Global => (Proof_In => X);

   procedure Nop2 (S : in out String)
   with Post => S(S'First .. X)'Old'Update (1 => 'X') = "123",
        Global => (Proof_In => X);
end;
