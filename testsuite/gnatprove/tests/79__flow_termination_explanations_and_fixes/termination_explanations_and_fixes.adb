package body termination_explanations_and_fixes with SPARK_Mode is

   procedure Nullify (X : in out Natural) is
      J : Natural := X;
   begin
      loop
         exit when J = 0;
         J := J - 1;
      end loop;
      X := J;
   end Nullify;

   procedure Use_Acc_To_F is
   begin
      declare
         Acc : Acc_To_F := F'Access;
      begin
         Y := Acc.all;
      end;
   end Use_Acc_To_F;

   procedure P is null;

   procedure Use_Acc_To_P is
   begin
      declare
         Acc : Acc_To_P := P'Access;
      begin
         Acc.all;
      end;
   end Use_Acc_To_P;

   function Dispatching_F (X : in Tagged_Natural) return Natural is
   begin
      return X.E;
   end Dispatching_F;

   procedure Dispatching_P (X : out Tagged_Natural) is
   begin
      X.E := 0;
   end Dispatching_P;

   procedure Use_Dispatching_F is
   begin
      Y:= Dispatching_F (Z);
   end Use_Dispatching_F;

   procedure Use_Dispatching_P is
   begin
      Dispatching_P (Z);
   end Use_Dispatching_P;

   function F_Rec (X : Natural) return Natural is
   begin
      if X = 0 then
         return 0;
      else
         return F_Rec (X - 1);
      end if;
   end F_Rec;

   function A (X : Natural) return Natural is
   begin
      if X = 0 then
         return 0;
      else
         return B (X - 1);
      end if;
   end A;

   function B (X : Natural) return Natural is
   begin
      if X = 0 then
         return 0;
      else
         return A (X - 1);
      end if;
   end B;

   procedure P_Callee is null with SPARK_Mode => Off;

   function F_Caller return Natural is
   begin
      P_Callee;
      return 0;
   end F_Caller;

end termination_explanations_and_fixes;
