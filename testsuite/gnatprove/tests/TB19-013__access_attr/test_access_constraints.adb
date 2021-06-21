procedure Test_Access_Constraints with SPARK_Mode is
   type Rec (B : Boolean) is record
      F1, F2 : aliased Integer;
   end record;

   type Int_Array is array (Positive range <>) of Integer;

   procedure Test_Discr with Global => null is
      R : aliased Rec := (True, 1, 2);
   begin
      declare
         B : access Rec := R'Access;
      begin
         B.all := (False, 4, 5); --@DISCRIMINANT_CHECK:FAIL
      end;
   end Test_Discr;

   procedure Test_Discr (R : aliased in out Rec) with Global => null is
   begin
      declare
         B : access Rec := R'Access;
      begin
         B.all := (False, 4, 5); --@DISCRIMINANT_CHECK:FAIL
      end;
   end Test_Discr;

   procedure Test_Bounds with Global => null is
      A : aliased Int_Array := (1 .. 4 => 0);
   begin
      declare
         B : access Int_Array := A'Access;
      begin
         B.all := (1, 5); --@LENGTH_CHECK:FAIL
      end;
   end Test_Bounds;

   procedure Test_Bounds (A : aliased in out Int_Array) with Global => null is
   begin
      declare
         B : access Int_Array := A'Access;
      begin
         B.all := (1, 5); --@LENGTH_CHECK:FAIL
      end;
   end Test_Bounds;
begin
   null;
end Test_Access_Constraints;
