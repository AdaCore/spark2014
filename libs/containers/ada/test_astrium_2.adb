package body Test_Astrium_2 is

   function Test_Recovery_Highest (S : Set) return Recovery is
   begin
      return Element(Last(S));
   end Test_Recovery_Highest;

end Test_Astrium_2;
