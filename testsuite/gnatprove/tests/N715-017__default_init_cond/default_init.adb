with Private_Default; use Private_Default;

package body Default_Init with SPARK_Mode is

   function Init (X : Natural) return Natural is
   begin
      return Natural'Last - X;
   end Init;

   procedure Def_Priv is
      P1 : Simple_Priv;
      P2 : Wrong_Priv;
      P3 : Priv_With_Glob;
   begin
      pragma Assert (Simple_Priv_Ok (P1));
      pragma Assert (Wrong_Priv_Ok (P2));
      pragma Assert (Priv_With_Glob_Ok (P3));
      Set_Glob (1);
      pragma Assert (Simple_Priv_Ok (P1));
      pragma Assert (Wrong_Priv_Ok (P2));
      pragma Assert (Priv_With_Glob_Ok (P3)); --@ASSERT:FAIL
   end Def_Priv;

   procedure Def_Simple is
      R : Rec;
      N : Nat;
      A : Arr;
   begin
      pragma Assert (R.F = 0);
      pragma Assert (N = 0);
      pragma Assert (A (1) = 0);
   end Def_Simple;

   procedure Def_Wrong is
      W : Wrong;
   begin
      pragma Assert (W = Wrong (Init (0)));
   end Def_Wrong;

   procedure Def_Rte is
      R : Rte;
   begin
      if N in 1 .. 3 then
         pragma Assert (R (N) = 0);
      end if;
   end Def_Rte;

   procedure Def_Glob1 is
      G : Glob1;
   begin
      pragma Assert (G.F = N);
   end Def_Glob1;

   procedure Def_Glob2 is
   begin
      N := 0;
      declare
         G : Glob2;
      begin
         pragma Assert (G.F = N);
      end;
   end Def_Glob2;

   procedure Def_Discr is
      D1 : Discr (True);
      D2 : Discr (False);
      D3 : Mut_Discr;
      D4 : Mut_Discr (False);
      D5 : Mut_Discr (True);
   begin
      pragma Assert (D1.F = 0);
   end Def_Discr;
end;
