procedure Main with SPARK_Mode is
   type Rec is record
      X : Integer;
      Y : Integer;
   end record;

   X : Rec with Relaxed_Initialization;
   Y : Rec := (others => 1);

   type Root is tagged record
      F : Integer;
   end record;

   type Child is new Root with record
      G : Rec;
   end record;

   R : Root := (F => 1);

   procedure Test1 with Global => (Input => (X, R)) is
      C : Child := (R with G => X); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test1;

   procedure Test2 with Global => (Input => X) is
      Z : Rec := (X with delta Y => 1); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test2;

   C : Child := (R with G => Y);

   procedure Test3 with Global => (Input => (X, C)) is
      D : Child := (C with delta G => X); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test3;

   procedure Test4 with Global => (Input => X) is
      Y : Rec := X'Update (Y => 1); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test4;

   procedure Test5 with Global => (Input => (X, C)) is
      D : Child := C'Update (G => X); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test5;

   procedure Test6 (B : Boolean) with Global => (Input => (X, Y)) is
      Z : Rec := (case B is
                     when True => X, --@INIT_BY_PROOF:FAIL
                     when others => Y);
   begin
      null;
   end Test6;

   procedure Test7 (B : Boolean) with Global => (Input => (X, Y)) is
      Z : Rec := (case B is
                     when True => Y,
                     when others => X); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test7;

   procedure Test12 with Global => (Input => X) is
      Z : Rec := (X with delta Y => 1) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      W : Rec := (Z with delta X => 1); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test12;

   type Holder is record
      F : Integer;
      G : Rec;
   end record;

   H : Holder := (F => 1, G => Y);

   procedure Test13 with Global => (Input => (X, H)) is
      D : Holder := (H with delta G => (X with delta X => 1)) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      E : Holder := (D with delta G => (D.G with delta Y => 1)); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test13;

   procedure Test14 with Global => (Input => X) is
      Y : Rec := X'Update (Y => 1) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      Z : Rec := Y'Update (X => 1); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test14;

   procedure Test15 with Global => (Input => (X, H)) is
      D : Holder := H'Update (G => X'Update (X => 1)) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      E : Holder := D'Update (G => D.G'Update (Y => 1)); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test15;

   procedure Test16 (B : Boolean) with Global => (Input => (X, Y)) is
      Z : Rec := (case B is
                     when True => X, --@INIT_BY_PROOF:NONE
                     when others => Y) with Relaxed_Initialization;
   begin
      null;
   end Test16;

   procedure Test17 (B : Boolean) with Global => (Input => (X, Y)) is
      Z : Rec := (case B is
                     when True => Y,
                     when others => X) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
   begin
      null;
   end Test17;
begin
   null;
end Main;
