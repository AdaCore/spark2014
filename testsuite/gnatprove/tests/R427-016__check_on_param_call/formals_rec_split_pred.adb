procedure Formals_Rec_Split_Pred with SPARK_Mode is
   type Rec (D : Boolean) is record
      case D is
      when True =>
         F : Integer := 1;
         G : Integer := 1;
         H : Natural := 1;
      when False =>
         null;
      end case;
   end record;

   subtype Constr_Rec is Rec (True) with
     Predicate => Constr_Rec.H /= 0;

   type Constr_Rec_2 is new Rec (True) with
     Predicate => Constr_Rec_2.H /= 0;

   procedure P (A : in out Constr_Rec) with
     Pre => True
   is
   begin
      A.F := A.G / A.H;
   end P;

   procedure P (A : in out Constr_Rec_2) with
     Pre => True
   is
   begin
      A.F := A.G / A.H;
   end P;

   procedure P2 (A : in out Rec) with
     Pre => True
   is
   begin
      if A.D then
         A.H := 0;
      end if;
   end P2;

   procedure P3 (A : in out Constr_Rec) is
   begin
      A.F := A.G / A.H; --@PREDICATE_CHECK:FAIL
   end P3;

   procedure P3 (A : in out Constr_Rec_2) is
   begin
      A.F := A.G / A.H; --@PREDICATE_CHECK:FAIL
   end P3;

   procedure P4 (A : in out Rec) is
   begin
      if A.F = 0 then
         A.H := 0; --@PREDICATE_CHECK:FAIL
      end if;
   end P4;

   procedure P5 (A : in out Rec) is
   begin
      if A.F = 0 then
         A.H := 0; --@PREDICATE_CHECK:FAIL
      end if;
   end P5;

   X : Rec := (D => True, others => 1);
   Y : Constr_Rec := (D => True, others => 1);
   U : Constr_Rec := (D => True, others => 1);
begin
   P (X);
   P2 (X);
   P2 (X);
   P (X); --@PREDICATE_CHECK:FAIL
   P2 (X);
   P (Constr_Rec (X)); --@PREDICATE_CHECK:FAIL
   P (Y);
   P2 (Y); --@PREDICATE_CHECK:FAIL
   P (Y);
   P2 (Rec (Y)); --@PREDICATE_CHECK:FAIL
   P (U);
   P2 (Rec (U)); --@PREDICATE_CHECK:FAIL
   P (Y);
   P4 (Rec (Y));
   P2 (X);
   P3 (Constr_Rec (X));
   P (U);
   P5 (Rec (U));
   P2 (X);
   P3 (Constr_Rec_2 (X));
end Formals_Rec_Split_Pred;
