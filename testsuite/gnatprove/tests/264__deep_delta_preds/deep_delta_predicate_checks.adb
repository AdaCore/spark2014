procedure Deep_Delta_Predicate_Checks with SPARK_Mode is

   --  Predicate checks on simple aggregates with only record components

   procedure Test_Record_Preds with Global => null is
      type R1 is record
         F1, F2, F3 : Integer;
      end record
        with Predicate => F1 <= F2 and F2 <= F3;
      type R2 is record
         G1, G2, G3 : R1;
      end record
        with Predicate => G1.F3 <= G2.F1 and G2.F3 <= G3.F1 ;

      --  Predicate check on the enclosing record

      procedure Bad_1 with Global => null is
      X : R2 := (others => (others => 1));
      Y : R2 := (X with delta G2.F2 => 2, G2.F3 => 3); -- @PREDICATE_CHECK:FAIL
      begin
         null;
      end Bad_1;

      --  Predicate check on nested records

      procedure Bad_2 with Global => null is
      X : R2 := (others => (others => 1));
      Y : R2 := (X with delta G2.F2 => 2, G3 => (others => 4)); -- @PREDICATE_CHECK:FAIL
      begin
         null;
      end Bad_2;

      X : R2 := (others => (others => 1));
      Y : R2 := (X with delta G2.F2 => 2, G2.F3 => 3, G3 => (others => 4));
      Z : R2 := ((others => 1), (1, 2, 3), (others => 4));
   begin
      pragma Assert (Y = Z);
      pragma Assert (Y = X); -- @ASSERT:FAIL
   end Test_Record_Preds;

   --  Check that we emit predicate check in the general case

   procedure Test_Array_Preds (I, J, K, C : Integer) with
     Global => null,
     Pre => I in 1 .. C and J in 1 .. C and K in 1 .. C
   is
      type R1_B is record
         F1, F2, F3 : Integer;
      end record;
      subtype R1 is R1_B
        with Predicate => R1.F1 <= R1.F2 and R1.F2 <= R1.F3;
      type R2 is record
         G1 : R1;
         G2, G3 : Integer;
      end record
        with Predicate => G1.F3 <= G2 and G2 <= G3;
      type R2_Arr is array (Integer range 1 .. C) of R2
        with Predicate => (for all J in 1 .. C => R2_Arr (J).G3 <= 40);
      type R3 is record
         H1 : R2_Arr;
         H2 : Integer;
      end record
        with Predicate => (for all J in 1 .. C => H1 (J).G3 <= H2);

      --  Predicate check on a leaf

      procedure Bad_1 with
        Global => (I, C),
        Pre => I in 1 .. C
      is
         X : R3 := (H1 => (others => (G1 => (others => 8), others => 8)), H2 => 8);
         Y : R3 := (X with delta H1 (I).G1.F3 => 2); -- @PREDICATE_CHECK:FAIL
      begin
         null;
      end Bad_1;

      --  No predicate checks are performed for temporary values

      procedure OK_1 with
        Global => (I, J, C),
        Pre => I in 1 .. C and J = I
      is
         X : R3 := (H1 => (others => (G1 => (others => 8), others => 8)), H2 => 8);
         Y : R3 := (X with delta
                      H1 (I).G1.F3 => 2, -- @PREDICATE_CHECK:PASS
                      H1 (J).G1.F3 => 8);
      begin
         null;
      end OK_1;

      --  Predicate check on overlapping values

      procedure Bad_2 with
        Global => (I, J, C),
        Pre => I in 1 .. C and J in 1 .. C
      is
         X : R3 := (H1 => (others => (G1 => (1, 8, 8), others => 8)), H2 => 8);
         Y : R3 := (X with delta
                      H1 (I).G1.F1 => 5, -- @PREDICATE_CHECK:FAIL
                      H1 (J).G1.F2 => 4);
      begin
         null;
      end Bad_2;

      --  Predicate check on internal nodes

      procedure Bad_3 with
        Global => (I, J, C),
        Pre => I in 1 .. C and J in 1 .. C
      is
         X : R3 := (H1 => (others => (G1 => (1, 8, 8), G2 => 8, G3 => 12)), H2 => 14);
         Y : R3 := (X with delta
                      H1 (I).G1.F1 => 4, -- @PREDICATE_CHECK:FAIL
                      H1 (J).G1.F3 => 10);
      begin
         null;
      end Bad_3;

      procedure Bad_4 with
        Global => (I, C),
        Pre => I in 1 .. C
      is
         X : R3 := (H1 => (others => (G1 => (1, 8, 8), G2 => 15, G3 => 16)), H2 => 80);
         Y : R3 := (X with delta H1 (I).G3 => 50); -- @PREDICATE_CHECK:FAIL
      begin
         null;
      end Bad_4;

      --  Predicate check on the assigned value

      procedure Bad_5 with
        Global => (I, C),
        Pre => I in 1 .. C
      is
         X : R3 := (H1 => (others => (G1 => (others => 8), others => 8)), H2 => 8);
         V : R1_B := (4, 2, 3);
         Y : R3 := (X with delta H1 (I).G1 => V); -- @PREDICATE_CHECK:FAIL
      begin
         null;
      end Bad_5;

      --  It should occur even if the value is corrected afterward as a
      --  predicate check could fail at runtime.

      procedure Bad_6 with
        Global => (I, J, C),
        Pre => I in 1 .. C and I = J
      is
         X : R3 := (H1 => (others => (G1 => (others => 8), others => 8)), H2 => 8);
         V : R1_B := (4, 2, 3);
         Y : R3 := (X with delta
                      H1 (I).G1 => V, -- @PREDICATE_CHECK:FAIL
                      H1 (J).G1.F1 => 1);
      begin
         null;
      end Bad_6;

      X : R3 := (H1 => (others => (G1 => (others => 8), others => 8)), H2 => 8);
      Y : R3 := (X with delta
                   H1 (I).G1.F1 => 2,
                   H1 (J).G1.F1 => 3,
                   H1 (K).G1.F1 => 4);
      Z : R3 := X;
   begin
      Z.H1 (I).G1.F1 := 2;
      Z.H1 (J).G1.F1 := 3;
      Z.H1 (K).G1.F1 := 4;
      pragma Assert (Y = Z);
      pragma Assert (Y = X); -- @ASSERT:FAIL
   end Test_Array_Preds;
begin
   null;
end Deep_Delta_Predicate_Checks;
