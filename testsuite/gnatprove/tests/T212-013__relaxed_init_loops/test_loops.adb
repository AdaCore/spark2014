procedure Test_Loops with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Rec is record
      F1, F2, F3 : Integer;
   end record;

   type Arr_Rec is array (Positive range <>) of Rec;

   type Two_Arrs (Max : Natural) is record
      G1 : Arr_Rec (1 .. Max);
      G2 : Rec;
   end record;

   type A_Part_Init is new Arr_Rec with Relaxed_Initialization;
   type R_Part_Init is new Rec with Relaxed_Initialization;

   procedure Init_F2 (X : in out R_Part_Init) with
     Post => X.F2'Initialized
     and then X.F1'Initialized = X.F1'Initialized'Old
     and then X.F3'Initialized = X.F3'Initialized'Old
   is
   begin
      X.F2 := 15;
   end Init_F2;

   procedure Init_F3 (X : in out R_Part_Init) with
     Pre  => X.F1'Initialized and X.F2'Initialized,
     Post => X'Initialized
   is
   begin
      X.F3 := 15;
   end Init_F3;

   procedure Init_F1 (X : out R_Part_Init) with
     Post => X.F1'Initialized
   is
   begin
      X.F1 := 15;
   end Init_F1;

   procedure Init_One (X : in out A_Part_Init; I : Positive) with
     Pre  => I in X'Range,
     Post => X (I).F1'Initialized
     and then (for all K in X'Range =>
                 (if I /= K then X (K).F1'Initialized = X'Old (K).F1'Initialized))
     and then (for all K in X'Range =>
                 (X (K).F2'Initialized = X'Old (K).F2'Initialized
                      and X (K).F3'Initialized = X'Old (K).F3'Initialized))
   is
   begin
      X (I).F1 := 15;
   end Init_One;

   procedure Init_First (X : out A_Part_Init; I : Positive)
   is
      R : A_Part_Init (X'First .. X'Last);
   begin
      Init_F1 (R_Part_Init (R (I)));
      X := R; --@INIT_BY_PROOF:FAIL
   end Init_First;

   procedure Init_All_Bad (X : out Two_Arrs) with
     Pre => X.Max > 2
   is
   begin
      Init_F1 (R_Part_Init (X.G2)); --@INIT_BY_PROOF:FAIL
      Init_F2 (R_Part_Init (X.G2));
      Init_F3 (R_Part_Init (X.G2));

      for I in reverse 1 .. X.Max loop
         X.G1 (I).F2 := I;
      end loop;
      Init_First (A_Part_Init (X.G1), 1);
      for I in 2 .. X.Max loop
         Init_One (A_Part_Init (X.G1), I);
      end loop;
      for I in reverse 1 .. X.Max loop
         X.G1 (I).F2 := I;
      end loop;
      for I in 1 .. X.Max loop
         Init_F3 (R_Part_Init (X.G1 (I)));
      end loop;
   end Init_All_Bad;


   procedure Init_All (X : out Two_Arrs) with
     Pre => X.Max > 2
   is
      C : constant Integer := X.Max;
      type T_Part_Init is new Two_Arrs (C) with Relaxed_Initialization;
      procedure Nested (X : out T_Part_Init) with
        Pre  => X.Max > 2,
        Post => X'Initialized
      is
      begin
         Init_F1 (R_Part_Init (X.G2));
         Init_F2 (R_Part_Init (X.G2));
         Init_F3 (R_Part_Init (X.G2));

         Init_First (A_Part_Init (X.G1), 1);
         for I in 2 .. X.Max loop
            Init_One (A_Part_Init (X.G1), I);
            pragma Loop_Invariant (for all K in 1 .. I => X.G1 (K).F1'Initialized);
         end loop;
         for I in reverse 1 .. X.Max loop
            X.G1 (I).F2 := I;
            pragma Loop_Invariant (for all K in 1 .. X.Max => X.G1 (K).F1'Initialized);
            pragma Loop_Invariant (for all K in I .. X.Max => X.G1 (K).F2'Initialized);
         end loop;
         for I in 1 .. X.Max loop
            Init_F3 (R_Part_Init (X.G1 (I)));
            pragma Loop_Invariant (for all K in 1 .. X.Max => X.G1 (K).F1'Initialized and X.G1 (K).F2'Initialized);
            pragma Loop_Invariant (for all K in 1 .. I => X.G1 (K).F3'Initialized);
         end loop;
      end Nested;
   begin
      Nested (T_Part_Init (X));
   end Init_All;
begin
   null;
end Test_Loops;
