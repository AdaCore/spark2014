procedure Test_Accessibility_2 with SPARK_Mode is

   type Holder is record
      C : aliased Integer;
   end record;

   type Int_Acc is not null access Holder;

   type Rec is record
      F1 : aliased Integer;
      F2 : Int_Acc;
   end record;

   function Hidden_Access (X : aliased Integer) return not null access constant Integer with
     Post => Hidden_Access'Result.all = X
   is
   begin
      return X'Access; -- @ACCESSIBILITY_CHECK:NONE
   end Hidden_Access;

   function Id (X : not null access constant Integer) return not null access constant Integer with
     Post => Id'Result.all = X.all
   is
   begin
      return X; -- @ACCESSIBILITY_CHECK:PASS
   end Id;

   function Id (X : not null access constant Rec) return not null access constant Rec with
     Post => Id'Result.all = X.all
   is
   begin
      return X; -- @ACCESSIBILITY_CHECK:PASS
   end Id;

   function Hidden_Access (X : aliased Rec) return not null access constant Rec with
     Post => Hidden_Access'Result.all = X
   is
   begin
      return X'Access; -- @ACCESSIBILITY_CHECK:NONE
   end Hidden_Access;

   function OK1 (X : not null access constant Rec) return not null access constant Integer with
     Post => OK1'Result.all = X.F1
   is
   begin
      return X.F1'Access; -- @ACCESSIBILITY_CHECK:PASS
   end OK1;

   function OK1_bis (X : not null access constant Rec) return not null access constant Integer with
   --  Should be OK but is currently rejected by GNAT
     Post => OK1_bis'Result.all = X.F1
   is
   begin
      declare
         Res : access constant Integer := X.F1'Access;
      begin
         return Res; -- @ACCESSIBILITY_CHECK:PASS
      end;
   end OK1_bis;

   function KO2 (X : not null access constant Rec) return not null access constant Integer with
     Post => KO2'Result.all = X.F1
   is
   begin
      declare
         Obs : access constant Integer := X.F1'Access;
         Res : access constant Integer := Id (Obs);
      begin
         return Res; -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end KO2;

   function KO3 (X : not null access constant Rec) return not null access constant Integer with
     Post => KO3'Result.all = X.F1
   is
   begin
      declare
         Res : access constant Integer := Hidden_Access (X.F1);
      begin
         return Res; -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end KO3;

   function KO4 (X : not null access constant Rec) return not null access constant Integer with
     Post => KO4'Result.all = X.F1
   is
   begin
      declare
         Res : access constant Integer := Id (X).F1'Access;
      begin
         return Res; -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end KO4;

   function OK5 (X : not null access constant Rec) return not null access constant Integer with
     Post => OK5'Result.all = X.F2.C
   is
   begin
      declare
         Res : access constant Integer := X.F2.C'Access;
      begin
         return Res;
      end;
   end OK5;

   function KO6 (X : not null access constant Rec) return not null access constant Integer with
     Post => KO6'Result.all = X.F2.C
   is
   begin
      declare
         Obs : access constant Integer := X.F2.C'Access;
         Res : access constant Integer := Id (Obs);
      begin
         return Res; -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end KO6;

   function KO7 (X : not null access constant Rec) return not null access constant Integer with
     Post => KO7'Result.all = X.F2.C
   is
   begin
      declare
         Res : access constant Integer := Hidden_Access (X.F2.C);
      begin
         return Res; -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end KO7;

   function OK8 (X : not null access constant Rec) return not null access constant Integer with
     Post => OK8'Result.all = X.F2.C
   is
   begin
      declare
         Res : access constant Integer := Id (X).F2.C'Access;
      begin
         return Res;
      end;
   end OK8;

   function OK9 (X : not null access constant Rec) return not null access constant Integer with
   --  Should be OK but GNAT fails an accessibility check in the call to Id
     Post => OK9'Result.all = X.F1
   is
   begin
      declare
         Obs : access constant Integer := X.F1'Access;
      begin
         return Id (Obs); -- @ACCESSIBILITY_CHECK:PASS
      end;
   end OK9;

   function OK10 (X : not null access constant Rec) return not null access constant Integer with
     Post => OK10'Result.all = X.F2.C
   is
      Y : not null access constant Rec := X;
   begin
      return Hidden_Access (Y.F2.C);
   end OK10;

   function OK11 (X : not null access constant Rec) return not null access constant Integer with
     Post => OK11'Result.all = X.F1
   is
   begin
      return Hidden_Access (X.F1); -- @ACCESSIBILITY_CHECK:PASS
   end OK11;

   function OK12 (X : not null access constant Rec) return not null access constant Integer with
   --  Should be OK but GNAT fails an accessibility check in the call to Id
     Post => OK12'Result.all = X.F1
   is
   begin
      return Id (X).F1'Access; -- @ACCESSIBILITY_CHECK:PASS
   end OK12;

   function OK13 (X : not null access constant Rec) return not null access constant Integer with
     Post => OK13'Result.all = X.F1
   is
   begin
      return Hidden_Access (Id (X).F1); -- @ACCESSIBILITY_CHECK:PASS
   end OK13;

   procedure Test (R : aliased Rec) with
     Global => null,
     Pre => R.F1 = 1 and R.F2.C = 1
   is
      C   : access constant Rec := R'Access;
      I1  : access constant Integer := OK1 (C);
      I5  : access constant Integer := OK5 (C);
      I8  : access constant Integer := OK8 (C);
      I10 : access constant Integer := OK10 (C);
      I11 : access constant Integer := OK13 (C);
      I9 : access constant Integer := OK9 (C);
   begin
      pragma Assert (I1.all = 1);
      pragma Assert (I5.all = 1);
      pragma Assert (I8.all = 1);
      pragma Assert (I10.all = 1);
      pragma Assert (I11.all = 1);
   end Test;

   A  : Int_Acc := new Holder'(C => 1);
   R : aliased Rec := (1, A);
begin
   Test (R);
end Test_Accessibility_2;
