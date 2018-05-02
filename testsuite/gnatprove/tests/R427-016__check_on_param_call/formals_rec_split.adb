procedure Formals_Rec_Split (X, Y : Boolean; B1, B2 : Boolean) with SPARK_Mode is
   type Rec (D : Boolean) is record
      case D is
      when True =>
         F : Integer := 1;
      when False =>
         null;
      end case;
   end record;

   subtype Constr_Rec is Rec (X);

   subtype Constr_Rec_2 is Rec (Y);

   procedure P (A : out Constr_Rec) with
     Pre => True
   is
   begin
      if X then
         A.F := 1;
      end if;
   end P;

   procedure P2 (A : out Constr_Rec_2)
   is
   begin
      if Y then
         A.F := 1; -- @DISCRIMINANT_CHECK:FAIL
      end if;
   end P2;

   procedure P3 (A : out Constr_Rec_2)
   is
   begin
      if Y then
         A.F := 1; -- @DISCRIMINANT_CHECK:FAIL
      end if;
   end P3;

   V : Constr_Rec;
   U : Constr_Rec_2;
begin
   P (V);
   P2 (U);
   if B1 then
      if B2 then
         P (U); -- @DISCRIMINANT_CHECK:FAIL
      else
         P2 (V);
      end if;
   else
      if B2 then
         P (Rec (U)); -- @DISCRIMINANT_CHECK:FAIL
      else
         P3 (Rec (V));
      end if;
   end if;
end Formals_Rec_Split;
