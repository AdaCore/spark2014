procedure Test_Accessibility with SPARK_Mode is

   type Rec is record
      F1, F2 : aliased Integer;
   end record;

   function Hidden_Access (X : aliased Integer) return not null access constant Integer with
     Post => Hidden_Access'Result.all = X
   is
   begin
      return X'Access;
   end Hidden_Access;

   function Hidden_Access (X : aliased Rec) return not null access constant Rec with
     Post => Hidden_Access'Result.all = X
   is
   begin
      return X'Access;
   end Hidden_Access;

   function OK1 (X : not null access constant Rec) return not null access constant Integer with
     Post => OK1'Result.all = X.F1
   is
   begin
      declare
         Res : access constant Integer := X.F1'Access;
      begin
         return Res;
      end;
   end OK1;

   function OK2 (X : aliased Rec) return not null access constant Integer with
     Post => OK2'Result.all = X.F1
   is
   begin
      return X.F1'Access;
   end OK2;

   function OK3 (X : aliased Rec) return not null access constant Integer with
     Post => OK3'Result.all = X.F1
   is
   begin
      return Hidden_Access (X.F1);
   end OK3;

   type Rec_Acc is not null access Rec;

   function OK4 (X : Rec_Acc) return not null access constant Integer with
     Post => OK4'Result.all = X.F1
   is
      C : not null access constant Rec := X.all'Access;
   begin
      declare
         Res : access constant Integer := C.F1'Access;
      begin
         return Res;
      end;
   end OK4;

   function KO1 (X : aliased Rec) return not null access constant Integer with
     Post => KO1'Result.all = X.F1
   is
      C : not null access constant Rec := X'Access;
   begin
      declare
         Res : access constant Integer := C.F1'Access;
      begin
         return Res; -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end KO1;

   function KO2 (X : aliased Rec) return not null access constant Integer with
     Post => KO2'Result.all = X.F1
   is
   begin
      declare
         Res : access constant Integer := X.F1'Access;
      begin
         return Res; -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end KO2;

   function KO3 (X : aliased Rec) return not null access constant Integer with
     Post => KO3'Result.all = X.F1
   is
      C : not null access constant Rec := Hidden_Access (X);
   begin
      declare
         Res : access constant Integer := Hidden_Access (C.F1);
      begin
         return Res; -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end KO3;

   function KO4 (X : aliased Rec) return not null access constant Integer with
     Post => KO4'Result.all = X.F1
   is
   begin
      declare
         Res : access constant Integer := Hidden_Access (X.F1);
      begin
         return Res; -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end KO4;
begin
   null;
end Test_Accessibility;
