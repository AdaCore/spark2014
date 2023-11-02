procedure Deep_Delta_Relaxed with SPARK_Mode is

   --  Relaxed initialization in simple aggregates with only record components

   procedure Test_Record_Relaxed with Global => null is
      type R1 is record
         F1, F2, F3 : Integer;
      end record;
      type R2 is record
         G1, G2, G3 : R1;
      end record;

      --  Aggregate whose base has relaxed init

      procedure Relaxed_Base with Global => null is
         X : R2 with Relaxed_Initialization;
         Y : R2;
         Z : R2 with Relaxed_Initialization;
      begin
         X.G1 := (others => 1);
         X.G2.F1 := 1;
         X.G2.F3 := 1;
         Z := X;
         Z.G1.F1 := 2;
         Z.G2.F2 := 3;
         Z.G3 := (others => 4);
         pragma Assert (Z'Initialized);
         Y := (X with delta G1.F1 => 2, G2.F2 => 3, G3 => (others => 4));  -- @INIT_BY_PROOF:PASS
         pragma Assert (Y = Z);
         pragma Assert (Y = X); -- @ASSERT:FAIL
      end Relaxed_Base;

      --  Aggregate whose association has relaxed init

      procedure Relaxed_Comp with Global => null is
         X : R2 := (others => (others => 1));
         V : R1 with Relaxed_Initialization;
         Y : R2 := (X with delta G1.F1 => 2, G2.F2 => 3, G3 => V) with Relaxed_Initialization;
         Z : R2 := X with Relaxed_Initialization;
      begin
         Z.G1.F1 := 2;
         Z.G2.F2 := 3;
         Z.G3 := V;
         pragma Assert (Y.G1 = Z.G1);
         pragma Assert (Y.G2 = Z.G2);
         pragma Assert (Y.G3'Initialized); -- @ASSERT:FAIL
      end Relaxed_Comp;

      --  Initialization check on deep delta aggregate

      procedure Bad with Global => null is
         X : R2 with Relaxed_Initialization;
         Y : R2;
      begin
         X.G1 := (others => 1);
         X.G2.F1 := 1;
         Y := (X with delta G1.F1 => 2, G2.F2 => 3, G3 => (others => 4));  -- @INIT_BY_PROOF:FAIL
      end Bad;

   begin
      null;
   end Test_Record_Relaxed;

   --  Relaxed initialization in the general case

   procedure Test_Array_Relaxed (I, J, C : Integer) with
     Global => null,
     Pre => I in 1 .. C and J in 1 .. C
   is
      type R1 is record
         F1, F2, F3 : Integer;
      end record;
      type R2 is record
         G1 : R1;
         G2, G3 : Integer;
      end record;
      type R2_Arr is array (Integer range 1 .. C) of R2;
      type R3 is record
         H1 : R2_Arr;
         H2 : R1;
      end record;

      procedure Relaxed_Base with
        Global => (I, J, C),
        Pre => I in 1 .. C and J in 1 .. C
      is
         X : R3 with Relaxed_Initialization;
         V : R1 with Relaxed_Initialization;
         Y : R3;
         Z : R3 with Relaxed_Initialization;
      begin
         X.H1 := (others => (G1 => (others => 1), others => 1));
         X.H1 (J).G1 := (V with delta F1 => 1, F3 => 1);
         X.H1 (I).G1 := V;
         Y := (X with delta  --@INIT_BY_PROOF:PASS
                 H1 (I).G1 => (others => 2),
                 H1 (J).G1.F2 => 3,
                 H2 => (others => 4));
         Z := X;
         Z.H1 (I).G1 := (others => 2);
         Z.H1 (J).G1.F2 := 3;
         Z.H2 := (others => 4);
         pragma Assert (for all B in 1 .. C => Y.H1 (B) = Z.H1 (B));
         pragma Assert (Y = Z);
         pragma Assert (Y = X); -- @ASSERT:FAIL
      end Relaxed_Base;

      procedure Relaxed_Comp (K : Integer) with
        Global => (I, J, C),
        Pre => I in 1 .. C and J in 1 .. C and K in 1 .. C
      is
         X : R3 := (H1 => (others => (G1 => (others => 1), others => 1)), H2 => (others => 1));
         V : R1 with Relaxed_Initialization;
         Y : R3 := (X with delta
                      H1 (I).G1    => V,
                      H1 (J).G1.F2 => 3,
                      H2           => V) with Relaxed_Initialization;
         Z : R3 := X with Relaxed_Initialization;
      begin
         Z := X;
         Z.H1 (I).G1 := V;
         Z.H1 (J).G1.F2 := 3;
         Z.H2 := (others => 4);
         pragma Assert (if K /= I then Y.H1 (K) = Z.H1 (K));
         pragma Assert (Y.H1 (I)'Initialized or Y.H2'Initialized); -- @ASSERT:FAIL
      end Relaxed_Comp;

      procedure Bad (B : Boolean) with
        Global => (I, J, C),
        Pre => I in 1 .. C and J in 1 .. C
      is
         X : R3 with Relaxed_Initialization;
         V : R1 with Relaxed_Initialization;
         Y : R3;
      begin
         X.H1 := (others => (G1 => (others => 1), others => 1));
         X.H1 (I).G1 := V;
         X.H1 (J).G1 := (V with delta F1 => 1);
         if B then
            pragma Assert (X.H1 (J).G1.F3'Initialized); -- @ASSERT:FAIL
         else
            Y := (X with delta  --@INIT_BY_PROOF:FAIL
                    H1 (I).G1    => (others => 2),
                    H1 (J).G1.F2 => 3,
                    H2           => (others => 4));
         end if;
      end Bad;
   begin
      null;
   end Test_Array_Relaxed;

begin
   null;
end Deep_Delta_Relaxed;
