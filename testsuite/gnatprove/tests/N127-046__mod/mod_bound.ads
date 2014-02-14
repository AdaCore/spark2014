package Mod_Bound is

   type T is mod 2 ** 32;

   procedure Correct (X : in out T)
      with Post => X = T'First ;

   procedure Incorrect (X : in out T)
      with Post => X = T'First + 1;
end Mod_Bound;
