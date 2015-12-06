package body WWd_Char is

   --------------------------
   -- Wide_Width_Character --
   --------------------------

   function Wide_Width_Character (Lo, Hi : Character) return Natural is
      W : Natural;

   begin
      W := 0;
      for C in Lo .. Hi loop
         declare
            S : constant Wide_String := Character'Wide_Image (C);
         begin
            W := Natural'Max (W, S'Length);
         end;
      end loop;

      return W;
   end Wide_Width_Character;

end;
