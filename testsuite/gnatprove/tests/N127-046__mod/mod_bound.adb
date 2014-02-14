package body Mod_Bound is

   procedure Correct (X : in out T) is
   begin
      X := T'Last;
      X := X + 1;
   end Correct;

   procedure Incorrect (X : in out T) is
   begin
      X := T'Last;
      X := X + 1;
   end Incorrect;

end Mod_Bound;
