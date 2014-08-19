package body Dic2 is
   function Foo (Par : T) return Boolean is (Par = 0);

   function Bar (Par : U) return Boolean is (Par = 1);

   procedure Test is
      T_Var : T;
      U_Var : U;
      R_Var : R;
   begin
      pragma Assert (T_Var = R_Var.X and U_Var = R_Var.Y);
   end Test;
end Dic2;
