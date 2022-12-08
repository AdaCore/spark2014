procedure Test_Two_Preds with SPARK_Mode is

   --  Test case where several predicates apply to the same type with different
   --  Relaxed_Initialization policy.

   type T1 is record
      F, G : Integer;
   end record with
     Relaxed_Initialization,
     Predicate => F'Initialized or G'Initialized;

   procedure P (X : T1) is
      C : Integer;
   begin
      --  Not Ok, F might not be initialized
      C := X.F;  --@INIT_BY_PROOF:FAIL
   end P;

   type T2 is new T1 with
     Predicate => F > 0;

   procedure P (X : T2) with
     Relaxed_Initialization => X
   is
      C : Integer;
   begin
      --  Ok, the predicate of T2 implies initialization of F
      C := X.F; --@INIT_BY_PROOF:NONE --@PREDICATE_CHECK:NONE
   end P;

   type T3 is new T2 with Relaxed_Initialization;

   procedure P (X : T3) is
      C : Integer;
   begin
      --  Ok, the predicate of T2 implies initialization of F
      C := X.F; --@INIT_BY_PROOF:NONE --@PREDICATE_CHECK:NONE
   end P;

   type R is record
      B : Boolean;
      H : T2;
   end record;

   procedure P (X : R) with
     Relaxed_Initialization => X
   is
      C : Integer;
   begin
      --  Not Ok, X.H might not be initialized
      C := X.H.F; --@INIT_BY_PROOF:FAIL --@PREDICATE_CHECK:FAIL
   end P;

   procedure Q (X : R) with
     Relaxed_Initialization => X,
     Pre => X.H'Initialized
   is
      C : Integer;
   begin
      --  Ok, X.H is initialized
      C := X.H.F; ---@INIT_BY_PROOF:PASS --@PREDICATE_CHECK:PASS
   end Q;

   procedure S (X : R) with
     Relaxed_Initialization => X,
     Pre => X.H.F'Initialized and X.H.G'Initialized
   is
      C : Integer;
   begin
      --  Not Ok, the predicate if X.H might not hold
      C := X.H.F; --@PREDICATE_CHECK:FAIL
   end S;

   procedure T (X : R) with
     Relaxed_Initialization => X,
     Pre => X.H.F'Initialized
   is
      C : Integer;
   begin
      --  Not Ok, X.H might not be initialized
      C := X.H.F; --@INIT_BY_PROOF:FAIL
   end T;

   X1 : T1;
   X2 : T2;
   Y2 : T2 with Relaxed_Initialization;
   X3 : T3;
begin
   null;
end;
