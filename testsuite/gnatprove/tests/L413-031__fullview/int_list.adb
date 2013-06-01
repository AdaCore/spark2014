package body Int_List is
   procedure Add (L : in out List; I : My_Int) is
   begin
      Prepend (L, I);
   end Add;

   procedure Incr (L : in out List) is
      Copy : List := L;
      C    : Cursor := First (L);
   begin
      while Has_Element (L, C) loop
--         pragma Assert
--           (Strict_Equal (Right (L, C),Right (Copy, C))
--              and then
--            (for all D in Right (L, C).Iterate => Element (L, D) = Element (Copy, D))
--              and then
--           (for all D in Left (L, C).Iterate => Element (L, D) = Element (Copy, C) + 1));
         Replace_Element (L, C, Element (L, C) + 1);
         Next (L, C);
      end loop;
   end Incr;
end Int_List;
