package Superstrings is

   type Super_String (Max_Length : Positive) is record
      Current_Length : Natural := 0;
      Data           : String (1 .. Max_Length);
   end record;

   function "="
     (Left  : Super_String;
      Right : Super_String) return Boolean;

   function Equal
     (Left  : Super_String;
      Right : Super_String) return Boolean renames "=";


private
end Superstrings;
