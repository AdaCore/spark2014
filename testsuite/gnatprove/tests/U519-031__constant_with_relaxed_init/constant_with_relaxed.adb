procedure Constant_With_Relaxed with SPARK_Mode is
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

   H : Holder := (F => 1, G => Y);

   procedure Test1 with Global => (Input => (X, H)) is
      D : Holder := H'Update (G => X'Update (X => 1)) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      Z : Rec := D.G with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      E : Holder := D'Update (G => Z'Update (Y => 1)); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test1;

   procedure Test2 with Global => (Input => (X, H)) is
      D : Holder := H'Update (G => X'Update (X => 1)) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      Z : constant Rec := D.G with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      E : Holder := D'Update (G => Z'Update (Y => 1)); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test2;

   procedure Test3 with Global => (Input => (X, H)) is
      D : Holder := H'Update (G => X'Update (X => 1)) with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
      E : Holder := (declare
                       Z : constant Rec := D.G with Relaxed_Initialization; --@INIT_BY_PROOF:NONE
                     begin D'Update (G => Z'Update (Y => 1))); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test3;
begin
   null;
end Constant_With_Relaxed;
