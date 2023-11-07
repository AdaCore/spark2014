procedure Test with SPARK_Mode is
   type My_Int is new Integer with Relaxed_Initialization;

   type R is record
      F, G : Integer;
      H    : My_Int;
   end record;

   subtype S is R with
     Predicate => S.F < S.G;

   procedure Pred_OK_1 (X : R; B : out Boolean) with
     Relaxed_Initialization => X,
     Pre => X.F'Initialized and X.G'Initialized;

   procedure Pred_OK_1 (X : R; B : out Boolean) is
   begin
      B := X in S; -- @INIT_BY_PROOF:PASS
   end Pred_OK_1;

   procedure Eq_OK_1 (X, Y, Z : R; B : out Boolean) with
     Relaxed_Initialization => X,
     Pre => X.F'Initialized and X.G'Initialized and X.H'Initialized
     and Y.H'Initialized and Z.H'Initialized;

   procedure Eq_OK_1 (X, Y, Z : R; B : out Boolean) is
   begin
      B := X in Y | Z; -- @INIT_BY_PROOF:PASS
   end Eq_OK_1;

   procedure Pred_Bad_1 (X : R; B : out Boolean) with
     Relaxed_Initialization => X,
     Pre => X.F'Initialized and X.H'Initialized;

   procedure Pred_Bad_1 (X : R; B : out Boolean) is
   begin
      B := X in S; -- @INIT_BY_PROOF:FAIL
   end Pred_Bad_1;

   procedure Eq_Bad_1 (X, Y, Z : R; B : out Boolean) with
     Relaxed_Initialization => X,
     Pre => X.F'Initialized and X.G'Initialized
     and Y.H'Initialized and Z.H'Initialized;

   procedure Eq_Bad_1 (X, Y , Z: R; B : out Boolean) is
   begin
      B := X in Y | Z; -- @INIT_BY_PROOF:FAIL
   end Eq_Bad_1;

   type R2 is new R with
     Relaxed_Initialization;

   subtype S2 is R2 with
     Ghost,
     Predicate => S2.F'Initialized;

   procedure Pred_OK_2 (X : R2; B : out Boolean) with
     Ghost;

   procedure Pred_OK_2 (X : R2; B : out Boolean) is
   begin
      B := X in S2; -- @INIT_BY_PROOF:NONE
   end Pred_OK_2;

   procedure Eq_OK_2 (X, Y, Z : R2; B : out Boolean) with
     Pre => X.F'Initialized and X.G'Initialized and X.H'Initialized
     and Y.F'Initialized and Y.G'Initialized and Y.H'Initialized
     and Z.F'Initialized and Z.G'Initialized and Z.H'Initialized;

   procedure Eq_OK_2 (X, Y, Z : R2; B : out Boolean) is
   begin
      B := X in Y | Z; -- @INIT_BY_PROOF:PASS
   end Eq_OK_2;

   procedure Eq_Bad_2 (X, Y, Z : R2; B : out Boolean) with
     Pre => X.F'Initialized and X.G'Initialized
     and Y.F'Initialized and Y.G'Initialized and Y.H'Initialized
     and Z.F'Initialized and Z.G'Initialized and Z.H'Initialized;

   procedure Eq_Bad_2 (X, Y, Z : R2; B : out Boolean) is
   begin
      B := X in Y | Z; -- @INIT_BY_PROOF:FAIL
   end Eq_Bad_2;

   type R3 is new R;

   function "=" (X, Y : R3) return Boolean is (X.F = Y.F and X.G = Y.G);

   subtype S3 is R3 with
     Predicate => S3.F < S3.G;

   procedure Pred_OK_3 (X : R3; B : out Boolean) with
     Relaxed_Initialization => X,
     Pre => X.F'Initialized and X.G'Initialized;

   procedure Pred_OK_3 (X : R3; B : out Boolean) is
   begin
      B := X in S3; -- @INIT_BY_PROOF:PASS
   end Pred_OK_3;

   procedure Eq_OK_3 (X, Y, Z : R3; B : out Boolean) with
     Relaxed_Initialization => X,
     Pre => X.F'Initialized and X.G'Initialized;

   procedure Eq_OK_3 (X, Y, Z : R3; B : out Boolean) is
   begin
      B := X in Y | Z; -- @INIT_BY_PROOF:PASS
   end Eq_OK_3;

   procedure Pred_Bad_3 (X : R3; B : out Boolean) with
     Relaxed_Initialization => X,
     Pre => X.F'Initialized;

   procedure Pred_Bad_3 (X : R3; B : out Boolean) is
   begin
      B := X in S3; -- @INIT_BY_PROOF:FAIL
   end Pred_Bad_3;

   procedure Eq_Bad_3 (X, Y, Z : R3; B : out Boolean) with
     Relaxed_Initialization => X,
     Pre => X.F'Initialized;

   procedure Eq_Bad_3 (X, Y, Z : R3; B : out Boolean) is
   begin
      B := X in Y | Z; -- @INIT_BY_PROOF:FAIL
   end Eq_Bad_3;

   type RB4 is new R with
     Relaxed_Initialization;

   function "=" (X, Y : RB4) return Boolean is (True);

   type R4 is new RB4;

   subtype S4 is R4 with
     Predicate => S4.F < S4.G;

   procedure Pred_OK_4 (X : R4; B : out Boolean) with
     Relaxed_Initialization => X,
     Pre => X.F'Initialized and X.G'Initialized;

   procedure Pred_OK_4 (X : R4; B : out Boolean) is
   begin
      B := X in S4; -- @INIT_BY_PROOF:PASS
   end Pred_OK_4;

   procedure Eq_OK_4 (X, Y, Z : R4; B : out Boolean) with
     Relaxed_Initialization => X;

   procedure Eq_OK_4 (X, Y, Z : R4; B : out Boolean) is
   begin
      B := X in Y | Z; -- Here the initialization should be provable but it is
                       -- not as we decided to never use the init wrapper for
                       -- the type in _user_eq. This should not happen often
                       -- in practice as it is difficult to define a meaningful
                       -- equality on a type entirely uninitialized.
   end Eq_OK_4;

   procedure Pred_Bad_4 (X : R4; B : out Boolean) with
     Relaxed_Initialization => X,
     Pre => X.F'Initialized and X.H'Initialized;

   procedure Pred_Bad_4 (X : R4; B : out Boolean) is
   begin
      B := X in S4; -- @INIT_BY_PROOF:FAIL
   end Pred_Bad_4;

begin
   null;
end Test;
