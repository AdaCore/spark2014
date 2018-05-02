procedure Formals with SPARK_Mode is
   type My_Array is array (Integer range 1 .. 10) of Natural;
   type My_Int is new Integer range -10 .. 10;

   subtype Constr_Arr is My_Array with
     Predicate => Constr_Arr (3) /= 0;
   subtype Constr_Int is My_Int with
     Predicate => Constr_Int /= 0;

   type Constr_Arr_2 is new My_Array with
     Predicate => Constr_Arr_2 (3) /= 0;
   type Constr_Int_2 is new My_Int with
     Predicate => Constr_Int_2 /= 0;

   procedure P (A : in out Constr_Arr) with
     Pre => True
   is
   begin
      A (1) := A (2) / A (3);
   end P;

   procedure P (A : in out Constr_Arr_2) with
     Pre => True
   is
   begin
      A (1) := A (2) / A (3);
   end P;

   procedure P2 (A : in out My_Array) with
     Pre => True
   is
   begin
      A (3) := 0;
   end P2;

   procedure P3 (A : in out Constr_Arr) is
   begin
      A (1) := A (2) / A (3); --@PREDICATE_CHECK:FAIL
   end P3;

   procedure P3 (A : in out Constr_Arr_2) is
   begin
      A (1) := A (2) / A (3); --@PREDICATE_CHECK:FAIL
   end P3;

   procedure P4 (A : in out My_Array) is
   begin
      if A (1) = 0 then
         A (3) := 0; --@PREDICATE_CHECK:FAIL
      end if;
   end P4;

   procedure P5 (A : in out My_Array) is
   begin
      if A (1) = 0 then
         A (3) := 0; --@PREDICATE_CHECK:FAIL
      end if;
   end P5;

   procedure P (A : in out Constr_Int) with
     Pre => True
   is
   begin
      A := 10 / A;
   end P;

   procedure P (A : in out Constr_Int_2) with
     Pre => True
   is
   begin
      A := 10 / A;
   end P;

   procedure P2 (A : out My_Int) with
     Pre => True
   is
   begin
      A := 0;
   end P2;

   X : My_Array := (others => 1);
   Y : Constr_Arr := (others => 1);
   U : Constr_Arr_2 := (others => 1);

   Z : My_Int := 1;
   W : Constr_Int := 1;
   V : Constr_Int_2 := 1;
begin
   P (Z);
   P2 (Z);
   P2 (Z);
   P (Z); --@PREDICATE_CHECK:FAIL
   P2 (Z);
   P (Constr_Int (Z)); --@PREDICATE_CHECK:FAIL
   P (W);
   P2 (My_Int (W)); --@PREDICATE_CHECK:FAIL
   P2 (Z);
   P (Constr_Int_2 (Z)); --@PREDICATE_CHECK:FAIL
   P (V);
   P2 (My_Int (V)); --@PREDICATE_CHECK:FAIL
   P (W);
   P2 (W); --@PREDICATE_CHECK:FAIL
   P (X);
   P2 (X);
   P2 (X);
   P (X); --@PREDICATE_CHECK:FAIL
   P2 (X);
   P (Constr_Arr (X)); --@PREDICATE_CHECK:FAIL
   P (Y);
   P2 (Y); --@PREDICATE_CHECK:FAIL
   P (Y);
   P2 (My_Array (Y)); --@PREDICATE_CHECK:FAIL
   P (Y);
   P4 (My_Array (Y));
   P2 (X);
   P3 (Constr_Arr (X));
   P (U);
   P2 (My_Array (U)); --@PREDICATE_CHECK:FAIL
   P (U);
   P5 (My_Array (U));
   P2 (X);
   P3 (Constr_Arr_2 (X));
end Formals;
