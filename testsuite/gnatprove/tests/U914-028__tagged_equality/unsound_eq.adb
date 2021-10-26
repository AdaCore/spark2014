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
      function "=" (X, Y : GrandChild2) return Boolean is (X.F = Y.F and X.G = Y.G and X.H = Y.H);

      type Holder2 is record
         C : GrandChild2;
      end record;
      --  Predefined equality on Holder2 uses the primitive equality on
      --  GrandChild2, so it does compare field F.
   end P;
   use P;

   X  : GrandChild1 := (others => 1);
   Y  : GrandChild1 := (F => 2, others => 1);
   Z  : GrandChild1 := (H => 2, others => 1);
   H1 : Holder1 := (C => X);
   H2 : Holder1 := (C => Y);
   H3 : Holder2 := (C => (others => 1));
   H4 : Holder2 := (C => (F => 2, others => 1));
begin
   --  X and Y only differ by the F field, so the predefined equality on
   --  GrandChild1 returns True.
   pragma Assert (X = Y); --@ASSERT:PASS
   --  H1.C and H2.C only differ by the F field, so the predefined equality on
   --  Holder1 returns True.
   pragma Assert (H1 = H2); --@ASSERT:PASS
   --  H3.C and H4.C differ by the F field, so the predefined equality on
   --  Holder2 returns False.
   pragma Assert (H3 /= H4); --@ASSERT:PASS
   --  X and Z differ by the H field, so the predefined equality on GrandChild1
   --  returns False.
   pragma Assert (X = Z); --@ASSERT:FAIL
end;
