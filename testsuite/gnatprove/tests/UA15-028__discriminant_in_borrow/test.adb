procedure Test with SPARK_Mode is
   type Rec (P : Boolean) is null record;
   type Rec_Acc is access Rec;
   function At_End (X : access constant Rec) return access constant Rec is (X)
     with Ghost, Annotate => (GNATProve, At_End_Borrow);
   function Id (X : not null access Rec) return not null access Rec is
   begin
      return X;
   end Id;

   type Arr is array (Positive range <>) of Natural;
   type Arr_Acc is access Arr;
   function At_End (X : access constant Arr) return access constant Arr is (X)
     with Ghost, Annotate => (GNATProve, At_End_Borrow);
   function Id (X : not null access Arr) return not null access Arr is
   begin
      return X;
   end Id;

   function Id (X : Integer) return Integer is (X);
   type CArr is array (Positive range Id (1) .. 10) of Natural;
   type CArr_Acc is access CArr;
   function At_End (X : access constant CArr) return access constant CArr is (X)
     with Ghost, Annotate => (GNATProve, At_End_Borrow);
   function Id (X : not null access CArr) return not null access CArr is
   begin
      return X;
   end Id;

   type DRec (P : Boolean := True) is null record;
   type DRec_Acc is access DRec;
   function At_End (X : access constant DRec) return access constant DRec is (X)
     with Ghost, Annotate => (GNATProve, At_End_Borrow);
   function Id (X : not null access DRec) return not null access DRec is
   begin
      return X;
   end Id;

   X_Rec : aliased Rec_Acc := new Rec'(P => True);
   X_DRec : aliased DRec_Acc := new DRec'(P => True);
   X_Arr : aliased Arr_Acc := new Arr'(1 .. 10 => 0);
   X_CArr : aliased CArr_Acc := new CArr'(1 .. 10 => 0);
begin
   declare
      B_Rec : access Rec := X_Rec;
      B_DRec : access DRec := X_DRec;
      B_Arr : access Arr := X_Arr;
      B_CArr : access CArr := X_CArr;
   begin
      pragma Assert (At_End (X_Rec).P);
      pragma Assert (At_End (X_DRec).P); --@ASSERT:FAIL
      pragma Assert (At_End (X_Arr)'First = 1);
      pragma Assert (At_End (X_Arr)'Last = 10);
      pragma Assert (At_End (X_CArr)'First = 1);
      pragma Assert (At_End (X_CArr)'Last = 10);
   end;
   declare
      B_Rec : access Rec := Id (X_Rec);
      B_DRec : access DRec := Id (X_DRec);
      B_Arr : access Arr := Id (X_Arr);
      B_CArr : access CArr := Id (X_CArr);
   begin
      pragma Assert (At_End (X_Rec).P);
      pragma Assert (At_End (X_DRec).P); --@ASSERT:FAIL
      pragma Assert (At_End (X_Arr)'First = 1);
      pragma Assert (At_End (X_Arr)'Last = 10);
      pragma Assert (At_End (X_CArr)'First = 1);
      pragma Assert (At_End (X_CArr)'Last = 10);
      pragma Assert (At_End (B_Rec).P = B_Rec.P);
      pragma Assert (At_End (B_DRec).P = B_DRec.P); --@ASSERT:FAIL
      pragma Assert (At_End (B_Arr)'First = B_Arr'First);
      pragma Assert (At_End (B_Arr)'Last = B_Arr'Last);
      pragma Assert (At_End (B_CArr)'First = 1);
      pragma Assert (At_End (B_CArr)'Last = 10);
   end;
   declare
      B_Rec : access Rec_Acc := X_Rec'Access;
      B_DRec : access DRec_Acc := X_DRec'Access;
      B_Arr : access Arr_Acc := X_Arr'Access;
      B_CArr : access CArr_Acc := X_CArr'Access;
   begin
      pragma Assert (At_End (X_Rec).P); --@ASSERT:FAIL
      pragma Assert (At_End (X_DRec).P); --@ASSERT:FAIL
      pragma Assert (At_End (X_Arr)'First = 1); --@ASSERT:FAIL
      pragma Assert (At_End (X_Arr)'Last = 10); --@ASSERT:FAIL
      pragma Assert (At_End (X_CArr)'First = 1);
      pragma Assert (At_End (X_CArr)'Last = 10);
   end;
end;
