procedure Test_Pred with SPARK_Mode is

   type My_Rec is record
      X, Y, Z : Integer;
   end record;

   type My_Rec_2 is new My_Rec with Annotate => (GNATprove, Init_By_Proof);

   function Ignore (X : Integer) return Boolean is (True);

   type Holder is record
      C : My_Rec;
   end record
     with Predicate => C.X > 0 and Ignore (C.Y);

   procedure Test_1 with Global => null is
      X : My_Rec_2;
   begin
      X.Y := 10;
      X.Z := 15;
      pragma Assert (Holder'(C => My_Rec (X)).C.Y > 0); -- @INIT_BY_PROOF:FAIL
   end Test_1;

   procedure Test_2 (B : Boolean) with Global => null is
      X : My_Rec_2;
   begin
      X.X := 10;
      if B then
         X.Z := 15;
         pragma Assert (Holder'(C => My_Rec (X)).C.X > 0); -- @INIT_BY_PROOF:FAIL
      else
         X.Y := 15;
         pragma Assert (Holder'(C => My_Rec (X)).C.X > 0); -- @INIT_BY_PROOF:FAIL
         -- Even if Holder's predicate does not mention Z, it should still be initialized
         -- as checks of RTE in the predicate assumes it.
      end if;
   end Test_2;

   type Int is new Integer with Annotate => (GNATprove, Init_By_Proof);

   type My_Rec_N is record
      X, Z : Int;
      Y    : Integer;
   end record;

   type Holder_N is record
      C : My_Rec_N;
   end record
     with Predicate => (if C.X'Valid_Scalars then C.X > 0 and then Ignore (C.Y));

   type My_Rec_N_2 is new My_Rec_N with Annotate => (GNATprove, Init_By_Proof);

   procedure Test_3 with Global => null is
      X : My_Rec_N_2;
   begin
      X.Y := 10;
      X.Z := 15;
      pragma Assert (Holder_N'(C => My_Rec_N (X)).C.Y > 0); -- @INIT_BY_PROOF:PASS @PREDICATE_CHECK:FAIL
      --  No initialization check is introduced for Y which is known to have
      --  relaxed init while checking the predicate. The predicate is not
      --  provable because C.X'Valid_Scalars is not known to be False on
      --  uninitialized data (to match the executable semantics).
   end Test_3;

   procedure Test_4 (B : Boolean) with Global => null is
      X : My_Rec_N_2;
   begin
      X.X := 10;
      if B then
         X.Z := 15;
         pragma Assert (Holder_N'(C => My_Rec_N (X)).C.X > 0); -- @INIT_BY_PROOF:FAIL
      else
         X.Y := 15;
         pragma Assert (Holder_N'(C => My_Rec_N (X)).C.X > 0); -- @INIT_BY_PROOF:PASS
         --  Ok, Z is known to have relaxed init while checking the predicate
      end if;
   end Test_4;

   type My_Rec_D is record
      X, Z : Int;
      Y    : Integer;
   end record;

   type My_Rec_D_2 is new My_Rec_D with Annotate => (GNATprove, Init_By_Proof);

   subtype My_Rec_D_3 is My_Rec_D
     with Predicate => (if My_Rec_D_3.X'Valid_Scalars then My_Rec_D_3.X > 0 and then Ignore (My_Rec_D_3.Y));

   procedure Test_5 with Global => null is
      X : My_Rec_D_2;
   begin
      X.Y := 10;
      X.Z := 15;
      pragma Assert (My_Rec_D_3 (X).Y > 0); -- @INIT_BY_PROOF:PASS @PREDICATE_CHECK:FAIL
   end Test_5;

   type Holder_D is record
      C : My_Rec_D_3;
   end record;

   procedure Test_6 (B : Integer) with Global => null is
      X : My_Rec_D_2;
   begin
      X.X := 10;
      if B = 0 then
         X.Z := 15;
         pragma Assert (My_Rec_D_3 (X).X > 0); -- @INIT_BY_PROOF:FAIL
      elsif B = 1 then
         X.Y := 15;
         pragma Assert (My_Rec_D_3 (X).X > 0); -- @INIT_BY_PROOF:PASS
      elsif B = 2 then
         X.Z := 15;
         pragma Assert (My_Rec_D (X).X > 0);-- @INIT_BY_PROOF:PASS
         pragma Assert (My_Rec_D_3'(My_Rec_D (X)).X > 0); -- @INIT_BY_PROOF:FAIL
      elsif B = 3 then
         X.Y := 15;
         pragma Assert (My_Rec_D (X).X > 0);-- @INIT_BY_PROOF:PASS
         pragma Assert (My_Rec_D_3'(My_Rec_D (X)).X > 0); -- @INIT_BY_PROOF:PASS
      elsif B = 4 then
         X.Z := 15;
         pragma Assert (Holder_D'(C => My_Rec_D (X)).C.X > 0); -- @INIT_BY_PROOF:FAIL
      elsif B = 5 then
         X.Y := 15;
         pragma Assert (Holder_D'(C => My_Rec_D (X)).C.X > 0); -- @INIT_BY_PROOF:PASS
      end if;
   end Test_6;

begin
   null;
end Test_Pred;
