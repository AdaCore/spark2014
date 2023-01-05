procedure Test_Pred_On_Array with SPARK_Mode is
   type Element is new Integer with Relaxed_Initialization;
   type E_Arr is array (Positive range <>) of Element with
     Predicate => (for some I in E_Arr'Range => E_Arr (I)'Initialized);

   procedure Test (X : E_Arr) with Global => null is
   begin
      pragma Assert (if X'First = 1 and X'Last = 1 then X (1)'Initialized);
   end Test;

   procedure P1 (A : Positive) with Global => null is
      X : E_Arr (1 .. A);
   begin
      Test (X); -- @PREDICATE_CHECK:FAIL
   end P1;

   procedure Q1 (X : out E_Arr) with Global => null is -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Q1;

   function F1 (A : Positive) return E_Arr with Global => null is
      X : E_Arr (1 .. A);
   begin
      return X; -- @PREDICATE_CHECK:FAIL
   end F1;

   procedure P2 (A : Positive) with Global => null is
      X : E_Arr (1 .. A);
   begin
      X (1) := 15;
      Test (X); -- @PREDICATE_CHECK:PASS
   end P2;

   function F2 (A : Positive) return E_Arr with Global => null is
      X : E_Arr (1 .. A);
   begin
      X (1) := 15;
      return X; -- @PREDICATE_CHECK:PASS
   end F2;

   procedure Q2 (X : out E_Arr) with -- @PREDICATE_CHECK:PASS
     Global => null,
     Pre => 1 in X'Range
   is
   begin
      X (1) := 15;
   end Q2;

   type E_Rec is record
      X, Y, Z : Element;
   end record with
   Predicate => X'Initialized or Y'Initialized or Z'Initialized;

   procedure Test (X : E_Rec) with Global => null is
   begin
      pragma Assert (X.X'Initialized or X.Y'Initialized or X.Z'Initialized);
   end Test;

   procedure P3 with Global => null is
      X : E_Rec;
   begin
      Test (X); -- @PREDICATE_CHECK:FAIL
   end P3;

   procedure Q3 (X : out E_Rec) with Global => null is-- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Q3;

   function F3 return E_Rec with Global => null is
      X : E_Rec;
   begin
      return X; -- @PREDICATE_CHECK:FAIL
   end F3;

   procedure P4 with Global => null is
      X : E_Rec;
   begin
      X.Y := 15;
      Test (X); -- @PREDICATE_CHECK:PASS
   end P4;

   procedure Q4 (X : out E_Rec) with Global => null is-- @PREDICATE_CHECK:PASS
   begin
      X.Y := 15;
   end Q4;

   function F4 return E_Rec with Global => null is
      X : E_Rec;
   begin
      X.Y := 15;
      return X; -- @PREDICATE_CHECK:PASS
   end F4;

   type E_Scal is new Element with
     Relaxed_Initialization,
     Predicate => E_Scal'Initialized;

   procedure Test (X : E_Scal) with Global => null is
   begin
      pragma Assert (X'Initialized);
   end Test;

   procedure P5 with Global => null is
      X : E_Scal;
   begin
      Test (X); -- @INIT_BY_PROOF:FAIL
   end P5;

   procedure Q5 (X : out E_Scal) with Global => null is -- @INIT_BY_PROOF:FAIL
   begin
      null;
   end Q5;

   function F5 return E_Scal with Global => null is
      X : E_Scal;
   begin
      return X; -- @INIT_BY_PROOF:FAIL
   end F5;

   procedure P6 with Global => null is
      X : E_Scal;
   begin
      X := 15;
      Test (X); -- @INIT_BY_PROOF:PASS
   end P6;

   procedure Q6 (X : out E_Scal) with Global => null is-- @INIT_BY_PROOF:PASS
   begin
      X := 15;
   end Q6;

   function F6 return E_Scal with Global => null is
      X : E_Scal;
   begin
      X := 15;
      return X; -- @INIT_BY_PROOF:PASS
   end F6;
begin
   null;
end Test_Pred_On_Array;
