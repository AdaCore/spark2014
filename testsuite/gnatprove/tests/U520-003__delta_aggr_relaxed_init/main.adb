procedure Main with SPARK_Mode is
   type Rec is record
      X : Integer;
      Y : Integer;
   end record;

   X : Rec with Relaxed_Initialization;
   Y : Rec := (others => 1);

   type Holder is record
      F : Integer;
      G : Rec;
   end record;

   type Arr is array (Integer range 1 .. 2) of Rec;

   A : Arr := (others => Y);

   procedure Test1 with Global => (Input => (X, A)) is
      B : Arr := (A with delta 1 => X); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test1;

   procedure Test2 with Global => (Input => (X, A)) is
      B : Arr := A'Update (1 => X); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test2;

   procedure Test3 with Global => (Input => X) is
      I : Arr := (others => X); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test3;

   I : Arr := (others => X) with Relaxed_Initialization;

   procedure Test4 with Global => (Input => (Y, I)) is
      B : Arr := (I with delta 1 => Y); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test4;

   procedure Test5 with Global => (Input => (Y, I)) is
      B : Arr := I'Update (1 => Y); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test5;

   procedure Test11 with Global => (Input => (X, A)) is
      B : Arr := (A with delta 1 => X) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      C : Arr := (B with delta 1 => A (1)); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test11;

   procedure Test12 with Global => (Input => (X, A)) is
      B : Arr := A'Update (1 => X) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      C : Arr := B'Update (1 => A (1)); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test12;

   procedure Test14 with Global => (Input => (Y, I)) is
      B : Arr := (I with delta 1 => Y) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      C : Arr := (B with delta 2 => Y); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test14;

   procedure Test15 with Global => (Input => (Y, I)) is
      B : Arr := I'Update (1 => Y) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      C : Arr := B'Update (2 => Y); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test15;
begin
   null;
end Main;
