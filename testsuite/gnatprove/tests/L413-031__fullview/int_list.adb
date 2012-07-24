package body Int_List is
   procedure Add (L : in out List; I : My_Int) is
   begin
      L.Prepend (I);
   end Add;

   procedure Incr (L : in out List) is
      Copy : List := L;
      C    : Cursor := L.First;
   begin
      while L.Has_Element (C) loop
         pragma Assert
           (L.Right (C).Strict_Equal (Copy.Right (C))
              and then
            (for all D in L.Right (C).Iterate => L.Element (D) = Copy.Element (D))
              and then
           (for all D in L.Left (C).Iterate => L.Element (D) = Copy.Element (C) + 1));
         L.Replace_Element (C, L.Element (C) + 1);
         L.Next (C);
      end loop;
   end Incr;
end Int_List;
