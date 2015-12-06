package WWd_Char is
   pragma Pure;

   function Wide_Width_Character (Lo, Hi : Character) return Natural;
   --  Compute Wide_Width attribute for non-static type derived from
   --  Character. The arguments are the low and high bounds for the type.

end WWd_Char;
