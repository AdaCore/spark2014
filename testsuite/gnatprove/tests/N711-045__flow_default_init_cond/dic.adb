package body Dic is
   A : Pr_Record_T;
   B : Pr_Record_T2;
   C : Pr_Uninit_T;
   D : Pr_Liar_T;

   function Gimme_A_Pr_T return Pr_T is (Pr_T'(X => 0));

   function Evaluate (R : Pr_T) return Integer is (R.X);

   function Add (R : Pr_Record_T) return Integer is (R.X + R.Y);

   function Foo (Par : Pr_Record_T2) return Boolean is (Par.X + Par.Y = G);

   procedure Do_Stuff is
   begin
      if A.X + A.Y = 0 then
         C.X := B.X;
         C.Y := B.Y;
      else
         C.X := D.X;
         C.Y := D.Y;
      end if;
   end Do_Stuff;
begin
   G := 0;
end Dic;
