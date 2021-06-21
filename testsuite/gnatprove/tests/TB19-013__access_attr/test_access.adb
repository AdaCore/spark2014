procedure Test_Access with SPARK_Mode is
   type Rec is record
      F1, F2 : aliased Integer;
   end record;

   type Int_Acc is access constant Integer;

   --  access constant
   C : constant Rec := (1, 2);
   P : Int_Acc := C.F1'Access;
   pragma Assert (P.all = 1);

   type Int_Acc_Neg is not null access constant Integer with
     Predicate => Int_Acc_Neg.all < 0;

   procedure Test_Pred with Global => null is
      P : Int_Acc_Neg := C.F1'Access; -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Test_Pred;

   V : aliased Rec := (1, 2);

   --  traversal

   function F_Obs (X : aliased Rec) return not null access constant Integer with
     Post => F_Obs'Result.all = X.F1
   is
   begin
      return X.F1'Access;
   end F_Obs;

   function At_End (X : access constant Rec) return access constant Rec is (X)
     with
       Ghost,
       Annotate => (GNATprove, At_End_Borrow);

   function At_End (X : access constant Integer) return access constant Integer is (X)
     with
       Ghost,
       Annotate => (GNATprove, At_End_Borrow);

   function F_Bor (X : not null access Rec) return not null access Integer with
     Post => At_End (F_Bor'Result).all = At_End (X).F1
   is
   begin
      return X.F1'Access;
   end F_Bor;
begin
   --  observe

   declare
      Obs_1 : access constant Integer := V.F1'Access;
      Obs_2 : access constant Integer := C.F2'Access;
   begin
      pragma Assert (Obs_1.all = 1);
      pragma Assert (Obs_2.all = 2);
      V.F2 := 15;
   end;

   declare
      Obs_3 : access constant Integer := F_Obs (V);
   begin
      pragma Assert (Obs_3.all = 1);
   end;

   --  borrow

   declare
      B_1 : access Integer := V.F1'Access;
   begin
      pragma Assert (B_1.all = 1);
      B_1.all := 4;
      V.F2 := 15;
   end;
   pragma Assert (V.F1 = 4);

   declare
      V_B : constant access Rec := V'Access;
      B_3 : access Integer := F_Bor (V_B);
   begin
      pragma Assert (B_3.all = 4);
      B_3.all := 1;
      B_3 := B_3.all'Access;
      B_3.all := B_3.all + 1;
   end;

   pragma Assert (V.F1 = 2);
   pragma Assert (V.F2 /= 15); -- @ASSERT:FAIL
end Test_Access;
