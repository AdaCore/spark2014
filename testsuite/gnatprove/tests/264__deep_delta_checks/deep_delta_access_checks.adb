procedure Deep_Delta_Access_Checks with SPARK_Mode is

   --  Discriminant handling for simple aggregates with only record components

   procedure Test_Record_Discr with Global => null is
      type R1 (D : Boolean := True) is record
         F1 : Integer;
         case D is
         when True =>
            F2 : Integer;
         when False =>
            F3 : Integer;
         end case;
      end record;
      type R2 (D : Boolean := True) is record
         G1, G2 : R1;
         G3 : R1 (D);
      end record;

      --  Discriminant check on selector

      procedure Bad_1 with Global => null is
         X : R2 := (D => True, others => (D => True, others => 1));
         W : R2 := (X with delta G1.F1 => 2, G2.F3 => 3, G3 => (D => True, others => 4)); -- @DISCRIMINANT_CHECK:FAIL
      begin
         null;
      end Bad_1;

      --  Discriminant check on discriminant dependent component

      procedure Bad_2 with Global => null is
         X : R2 := (D => True, others => (D => True, others => 1));
         V : R2 := (X with delta G1.F1 => 2, G2.F2 => 3, G3 => (D => False, others => 4)); -- @DISCRIMINANT_CHECK:FAIL
      begin
         null;
      end Bad_2;

      X : R2 := (D => True, others => (D => True, others => 1));
      Y : R2 := (X with delta G1.F1 => 2, G2.F2 => 3, G3 => (X.G3 with delta F2 => 4));
      Z : R2 :=  X;
   begin
      Z.G1.F1 := 2;
      Z.G2.F2 := 3;
      Z.G3.F2 := 4;
      pragma Assert (Y = Z);
      pragma Assert (Y = X); -- @ASSERT:FAIL
   end Test_Record_Discr;

   --  Discriminant handling for the general case

   procedure Test_Array_Discr (I, J, C : Integer) with
     Global => null,
     Pre => I in 1 .. C and J in 1 .. C
   is
      type R1 (D : Boolean := True) is record
         F1 : Integer;
         case D is
         when True =>
            F2 : Integer;
         when False =>
            F3 : Integer;
         end case;
      end record;
      type R2 is record
         G1 : R1 (True);
         G2, G3 : Integer;
      end record;
      type R2_Arr is array (Integer range 1 .. C) of R2;
      type R3 (D : Boolean := True) is record
         H1 : R2_Arr;
         case D is
         when True =>
            H2 : Integer;
         when False =>
            H3 : Integer;
         end case;
      end record;

      --  Discriminant check on selector

      procedure Bad_1 (I, J : Integer) with
        Global => C,
        Pre => I in 1 .. C and J in 1 .. C
      is
         X : R3 := (D => True, H1 => (others => (G1 => (D => True, others => 1), others => 1)), H2 => 1);
         Y : R3 := (X with delta
                      H1 (I).G1 => (D => True, others => 2),
                      H1 (J).G1.F2 => 3,
                      H3 => 4); -- @DISCRIMINANT_CHECK:FAIL
      begin
         null;
      end Bad_1;

      --  Discriminant check on discriminant dependent component

      procedure Bad_2 (I, J : Integer) with
        Global => C,
        Pre => I in 1 .. C and J in 1 .. C
      is
         X : R3 := (D => True, H1 => (others => (G1 => (D => True, others => 1), others => 1)), H2 => 1);
         V : R1 := (D => False, others => 2);
         Y : R3 := (X with delta
                      H1 (I).G1 => V, -- @DISCRIMINANT_CHECK:FAIL
                      H1 (J).G1.F2 => 3,
                      H2 => 4);
      begin
         null;
      end Bad_2;

      X : R3 := (D => True, H1 => (others => (G1 => (D => True, others => 1), others => 1)), H2 => 1);
      Y : R3 := (X with delta
                   H1 (I).G1 => (D => True, others => 2),
                   H1 (J).G1.F2 => 3,
                   H2 => 4);
      Z : R3 := X;
   begin
      Z.H1 (I).G1 := (D => True, others => 2);
      Z.H1 (J).G1.F2 := 3;
      Z.H2 := 4;
      pragma Assert (Y = Z);
      pragma Assert (Y = X); -- @ASSERT:FAIL
   end Test_Array_Discr;

   --  Test that we emit checks for array indexes

   procedure Test_Indexes (C, I, J, K, L, M, N, P : Integer) with
     Global => null,
     Pre => I in 1 .. C and J in 1 .. C and L in 1 .. C
        and K in 1 .. 10 and P in 1 .. 10
   is
      type R1 is record
         F1, F2, F3 : Integer;
      end record;
      type R1_Arr is array (Integer range 1 .. 10) of R1;
      type R2 is record
         G1 : R1_Arr;
         G2, G3 : Integer;
      end record;
      type R2_Arr is array (Integer range 1 .. C) of R2;
      type R3 is record
         H1 : R2_Arr;
         H2 : Integer;
      end record;

      X : R3 :=
        (H1 => (others => (G1 => (others => (others => 1)), others => 1)),
         H2 => 1);
      Y : R3 := (X with delta
                   H1 (I).G1 => (others => (others => 2)),
                   H1 (J).G1 (K) => (others => 3),
                   H1 (L).G1 (M).F1 => 4,--  @INDEX_CHECK:FAIL
                   H1 (N).G1 (P).F2 => 5,--  @INDEX_CHECK:FAIL
                   H2 => 6);
   begin
      null;
   end Test_Indexes;
begin
   null;
end Deep_Delta_Access_Checks;
