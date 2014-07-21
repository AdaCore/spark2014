package body Dic is
   A : Pr_Record_T;
   B : Pr_Record_T2;
   C : Pr_Uninit_T;
   D : Pr_Liar_T;

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
