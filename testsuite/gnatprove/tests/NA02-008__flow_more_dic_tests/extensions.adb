package body Extensions is
   function Gimme_One return Priv_Ext is
      R : Root;
      P : Priv_Ext := (R with Y => 0, Z => 0);
   begin
      return P;
   end Gimme_One;

   function Gimme_One return Pub_Ext is
      R : Root;
      P : Pub_Ext := (R with Y => 0);
   begin
      return P;
   end Gimme_One;

   function Gimme_One return Illegal is
      R : Root_2  := Gimme_One;
      P : Illegal := (R with Y => 0, Z => 0);
   begin
      return P;
   end Gimme_One;
end Extensions;
