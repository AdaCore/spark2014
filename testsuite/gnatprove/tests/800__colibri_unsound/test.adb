package body Test
is

   function Ident (M : Univ_Int) return Univ_Int
     is
   begin
      pragma Unreferenced (M);
      return 0;
   end Ident;

   procedure Test
     (MI  : Univ_Int)
   is
   begin
      pragma Assert (Ident (0) mod MI = 0 mod MI); --@ASSERT:FAIL
   end Test;

end Test;
