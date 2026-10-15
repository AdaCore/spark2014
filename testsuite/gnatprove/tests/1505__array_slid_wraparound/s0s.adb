package body S0s
  with SPARK_Mode
is

   -----------------
   -- Lemma_False --
   -----------------

   procedure Lemma_False (A, B : Two; K : I) is
      subtype S is U (K .. K + 1);
   begin
      --  This branch is unreachable. Its sliding and logical equality terms
      --  must not introduce a contradiction through the array axioms.
      pragma
        Assert
          (if Small (K)
           then
             S (A) (K) = A (0)
             and S (B) (K) = B (0)
             and not Eq (S (A), S (B)));
   end Lemma_False;

   --  Exercise wraparound in the last dimension for each array dimensionality,
   --  keeping the others nonempty. Each false postcondition must remain unproved.

   ---------------------
   -- Lemma_False_2_2 --
   ---------------------

   procedure Lemma_False_2_2 (A, B : Two2; K : I) is
      subtype S is U2 (0 .. 1, K .. K + 1);
   begin
      pragma
        Assert
          (if Small (K)
           then
             S (A) (0, K) = A (0, 0)
             and S (B) (0, K) = B (0, 0)
             and not Eq (S (A), S (B)));
   end Lemma_False_2_2;

   ---------------------
   -- Lemma_False_3_3 --
   ---------------------

   procedure Lemma_False_3_3 (A, B : Two3; K : I) is
      subtype S is U3 (0 .. 1, 0 .. 1, K .. K + 1);
   begin
      pragma
        Assert
          (if Small (K)
           then
             S (A) (0, 0, K) = A (0, 0, 0)
             and S (B) (0, 0, K) = B (0, 0, 0)
             and not Eq (S (A), S (B)));
   end Lemma_False_3_3;

   ---------------------
   -- Lemma_False_4_4 --
   ---------------------

   procedure Lemma_False_4_4 (A, B : Two4; K : I) is
      subtype S is U4 (0 .. 1, 0 .. 1, 0 .. 1, K .. K + 1);
   begin
      pragma
        Assert
          (if Small (K)
           then
             S (A) (0, 0, 0, K) = A (0, 0, 0, 0)
             and S (B) (0, 0, 0, K) = B (0, 0, 0, 0)
             and not Eq (S (A), S (B)));
   end Lemma_False_4_4;

end S0s;
