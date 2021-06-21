procedure Test_Accessibility with SPARK_Mode is
   type Int_Acc is not null access Integer;

   type Rec is record
      F1 : aliased Integer;
      F2 : Int_Acc;
   end record;

   function "=" (X, Y : Rec) return Boolean is
     (X.F1 = Y.F1
      and then ((X.F2 = null) = (Y.F2 = null)
        and then (if X.F2 /= null then X.F2.all = Y.F2.all)));

   function Id (X : not null access constant Rec) return not null access constant Rec with
     Post => Id'Result.all = X.all
   is
   begin
      return X;
   end Id;

   function Id (X : not null access constant Integer) return not null access constant Integer with
     Post => Id'Result.all = X.all
   is
   begin
      return X;
   end Id;

   function KO_1 (X : not null access constant Rec) return not null access constant Integer with
     Post => KO_1'Result.all = X.F2.all
   is
   begin
      declare
         Res : access constant Integer := Id (X.F2);
      begin
         return Res; -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end KO_1;

   function KO_2 (X : not null access constant Rec) return not null access constant Integer with
     Post => KO_2'Result.all = X.F2.all
   is
   begin
      declare
         Res : access constant Integer := Id (X.F2);
      begin
         return Id (Res); -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end KO_2;

   function KO_3 (X : not null access constant Rec) return not null access constant Integer with
     Post => KO_3'Result.all = X.F2.all
   is
      Res : access constant Integer := Id (X.F2);
   begin
      return Id (Res); -- @ACCESSIBILITY_CHECK:FAIL
   end KO_3;

   function KO_4 (X : not null access constant Rec) return not null access constant Integer with
     Post => KO_4'Result.all = X.F2.all
   is
      Res : access constant Integer := Id (X.F2);
   begin
      return Res; -- @ACCESSIBILITY_CHECK:FAIL
   end KO_4;

   function OK_1 (X : not null access constant Rec) return not null access constant Integer with
     Post => OK_1'Result.all = X.F2.all
   is
   begin
      return Id (X.F2);
   end OK_1;

   function OK_2 (X : not null access constant Rec) return not null access constant Integer with
     Post => OK_2'Result.all = X.F2.all
   is
   begin
      declare
         Res : access constant Integer := Id (X).F2;
      begin
         return Res;
      end;
   end OK_2;

   procedure Test (X : not null access constant Rec) with Global => null is
      Obs1 : access constant Integer := OK_1 (X);
      Obs2 : access constant Integer := OK_2 (X);
      Obs3 : access constant Integer := KO_4 (X);
   begin
      pragma Assert (Obs1.all = Obs2.all);
   end Test;

   type Rec_Access is access Rec;

   A : Int_Acc := new Integer'(2);
   X : Rec_Access := new Rec'(1, A);
begin
   Test (X);
end Test_Accessibility;
