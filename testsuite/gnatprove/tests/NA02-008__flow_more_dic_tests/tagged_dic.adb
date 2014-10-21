package body Tagged_DIC is
   function Gimme_One return Root is
      R : Root;
   begin
      return R;
   end Gimme_One;

   function Gimme_One return Root_2 is
      R : Root_2 := (X => 0);
   begin
      return R;
   end Gimme_One;
end Tagged_DIC;
