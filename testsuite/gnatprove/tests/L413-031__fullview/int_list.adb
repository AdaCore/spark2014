package body Int_List is pragma SPARK_Mode (On);
   procedure Add (L : in out List; I : My_Int) is
   begin
      Prepend (L, I);
   end Add;

   procedure Incr (L : in out List) is
      C    : Cursor := First (L);
   begin
      while Has_Element (L, C) loop
         pragma Loop_Invariant
           (Has_Element (L'Loop_Entry, C) and then
            Length (L) = Length (L'Loop_Entry) and then
            Strict_Equal (Right (L, C), Right (L'Loop_Entry, C)));
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
