procedure Unsound_Eq with SPARK_Mode is
   package P is
      type Root is tagged record
         F : Integer;
      end record;

      type Child is new Root with record
         G : Integer;
      end record;
      function "=" (X, Y : Child) return Boolean is (X.G = Y.G);

      type GrandChild1 is new Child with record
         H : Integer;
      end record;
      --  Predefined equality on GrandChild1 uses the primitive equality
      --  on Child, so it does not compare field F.

      type Holder1 is record
         C : GrandChild1;
      end record;
      --  Predefined equality on Holder1 uses the predefined equality on
      --  GrandChild1, so it does not compare field F.

      type GrandChild2 is new Child with record
         H : Integer;
      end record;
      function "=" (X, Y : GrandChild2) return Boolean is
         (X.F = Y.F and X.G = Y.G and X.H = Y.H);

      type Holder2 is record
         C : GrandChild2;
      end record;
      --  Predefined equality on Holder2 uses the primitive equality on
      --  GrandChild2, so it does compare field F.
   end P;
   use P;

   G1_111 : GrandChild1 := (others => 1);
   G1_211 : GrandChild1 := (F => 2, others => 1);
   G1_112 : GrandChild1 := (H => 2, others => 1);
   H1_111 : Holder1 := (C => G1_111);
   H1_211 : Holder1 := (C => G1_211);
   H2_111 : Holder2 := (C => (others => 1));
   H2_211 : Holder2 := (C => (F => 2, others => 1));
   --  In object names prefixes stand for the types and suffixes for the values

begin
   --  Those differ by F; the predefined equality on GrandChild1 and Holder1
   --  ignore it.

   pragma Assert (H1_111 = H1_211); --@ASSERT:PASS
   pragma Assert (G1_111 = G1_211); --@ASSERT:PASS

   --  Those two differ by H; the predefined equality on GrandChild1 and
   --  Holder2 sees it.

   pragma Assert (H2_111 /= H2_211); --@ASSERT:PASS
   pragma Assert (G1_111 = G1_112); --@ASSERT:FAIL
end;
