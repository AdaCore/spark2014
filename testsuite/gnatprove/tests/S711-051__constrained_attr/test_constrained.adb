procedure Test_Constrained with SPARK_Mode is
   type CC (B : Boolean := False) is null record;
   type CC_H is record
      C : CC;
   end record;
   type CC_Acc is access CC_H;

   function Get_Constr (X : CC) return Boolean is
     (X'Constrained)
     with Post => Get_Constr'Result;

   function F return CC is
      X : CC;
   begin
      pragma Assert (not X'Constrained);
      pragma Assert (Get_Constr (X));
      return X;
   end F;
   function F_Acc return CC_Acc with
     Post => F_Acc'Result /= null
   is
      X : CC_Acc := new CC_H'(C => (B => False));
   begin
      return X;
   end F_Acc;
   function F_H return CC_H is
   begin
      return CC_H'(C => (B => False));
   end F_H;

   pragma Assert (F'Constrained);
   pragma Assert (not F_Acc.C'Constrained);
   pragma Assert (F_H.C'Constrained);

   subtype CC_2 is CC;

   procedure Do_Smthg (X : in out CC_2) with
     Pre => not X'Constrained
   is
   begin
      null;
   end Do_Smthg;

   procedure Do_Smthg_2 (X : in out CC) with
     Pre => not X'Constrained
   is
   begin
      pragma Assert (not X'Constrained);
      pragma Assert (CC_2'(X)'Constrained);
      Do_Smthg (CC_2 (X));
   end Do_Smthg_2;

   X : CC;
begin
   Do_Smthg_2 (X);
end Test_Constrained;
