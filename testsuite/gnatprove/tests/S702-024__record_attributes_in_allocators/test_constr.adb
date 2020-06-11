procedure Test_Constr with SPARK_Mode is
   type R (D : Boolean := False) is null record;
   type H is record
      C : R;
   end record;
   type H_Acc is access H;
   type I is record
      C : H_Acc;
   end record;

   function Create return R is
     (D => False);
   function Create return H is
     (C => (D => False));
   function Create return I with Post => Create'Result.C /= null;
   function Create return I with SPARK_Mode => Off is
      B : H_Acc := new H'(C => (D => False));
   begin
      return (C => B);
   end Create;

   procedure Test1 is
   begin
      pragma Assert (declare V : constant I := Create; begin V.C.C'Constrained);  --@ASSERT:FAIL
   end Test1;

   procedure Test2 is
   begin
      pragma Assert (not H'(Create).C'Constrained);  --@ASSERT:FAIL
   end Test2;

   procedure Test3 is
   begin
      pragma Assert (not R'(Create)'Constrained);  --@ASSERT:FAIL
   end Test3;

   procedure Test4 is
   begin
      pragma Assert (declare V : constant I := Create; begin not R'(V.C.C)'Constrained);  --@ASSERT:FAIL
   end Test4;
begin
   null;
end Test_Constr;
