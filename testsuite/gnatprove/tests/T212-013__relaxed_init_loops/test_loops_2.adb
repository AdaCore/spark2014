procedure Test_Loops_2 with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Rec is record
      F1, F2, F3 : Integer;
   end record;

   type Arr_Rec is array (Positive range <>) of Rec;

   type Two_Arrs (Max : Natural) is record
      G1 : Arr_Rec (1 .. Max);
      G2 : Rec;
   end record;

   procedure Init_F2 (X : in out Rec) with
     Relaxed_Initialization => (X),
     Post => X.F2'Initialized
     and then X.F1'Initialized = X.F1'Initialized'Old
     and then X.F3'Initialized = X.F3'Initialized'Old;

   procedure Init_F2 (X : in out Rec)
   is
   begin
      X.F2 := 15;
   end Init_F2;

   procedure Init_F3 (X : in out Rec) with
     Relaxed_Initialization => (X),
     Pre  => X.F1'Initialized and X.F2'Initialized,
     Post => X'Initialized;

   procedure Init_F3 (X : in out Rec)
   is
   begin
      X.F3 := 15;
   end Init_F3;

   procedure Init_F1 (X : out Rec) with
     Relaxed_Initialization => (X),
     Post => X.F1'Initialized;

   procedure Init_F1 (X : out Rec)
   is
   begin
      X.F1 := 15;
   end Init_F1;

   procedure Init_One (X : in out Arr_Rec; I : Positive) with
     Relaxed_Initialization => (X),
     Pre  => I in X'Range,
     Post => X (I).F1'Initialized
     and then (for all K in X'Range =>
                 (if I /= K then X (K).F1'Initialized = X'Old (K).F1'Initialized))
     and then (for all K in X'Range =>
                 (X (K).F2'Initialized = X'Old (K).F2'Initialized
                      and X (K).F3'Initialized = X'Old (K).F3'Initialized));

   procedure Init_One (X : in out Arr_Rec; I : Positive)
   is
   begin
      X (I).F1 := 15;
   end Init_One;

   procedure Init_First (X : out Arr_Rec; I : Positive) with
     Relaxed_Initialization => (X),
     Pre  => I in X'Range,
     Post => X (I).F1'Initialized;

   procedure Init_First (X : out Arr_Rec; I : Positive) is
   begin
      Init_F1 (X (I));
   end Init_First;

   procedure Init_All_Bad (X : out Two_Arrs) with
     Pre => X.Max > 2
   is
   begin
      Init_F1 (X.G2); --@INIT_BY_PROOF:FAIL
      Init_F2 (X.G2);
      Init_F3 (X.G2);

      for I in reverse 1 .. X.Max loop
         X.G1 (I).F2 := I;
      end loop;
      Init_One (X.G1, 1); --  Flow analysis should complain that X.G1 is not initialized
      for I in 2 .. X.Max loop
         Init_One (X.G1, I);
      end loop;
      for I in reverse 1 .. X.Max loop
         X.G1 (I).F2 := I;
      end loop;
      for I in 1 .. X.Max loop
         Init_F3 (X.G1 (I));
      end loop;
   end Init_All_Bad;


   procedure Init_All (X : out Two_Arrs) with
     Pre => X.Max > 2
   is
      procedure Nested (X : out Two_Arrs) with
        Relaxed_Initialization => (X),
        Pre  => X.Max > 2,
        Post => X'Initialized;

      procedure Nested (X : out Two_Arrs) is
      begin
         Init_F1 (X.G2);
         Init_F2 (X.G2);
         Init_F3 (X.G2);

         Init_First (X.G1, 1);
         for I in 2 .. X.Max loop
            Init_One (X.G1, I);
            pragma Loop_Invariant (for all K in 1 .. I => X.G1 (K).F1'Initialized);
         end loop;
         for I in reverse 1 .. X.Max loop
            X.G1 (I).F2 := I;
            pragma Loop_Invariant (for all K in 1 .. X.Max => X.G1 (K).F1'Initialized);
            pragma Loop_Invariant (for all K in I .. X.Max => X.G1 (K).F2'Initialized);
         end loop;
         for I in 1 .. X.Max loop
            Init_F3 (X.G1 (I));
            pragma Loop_Invariant (for all K in 1 .. X.Max => X.G1 (K).F1'Initialized and X.G1 (K).F2'Initialized);
            pragma Loop_Invariant (for all K in 1 .. I => X.G1 (K).F3'Initialized);
         end loop;
      end Nested;
   begin
      Nested (X);
   end Init_All;
begin
   null;
end Test_Loops_2;
