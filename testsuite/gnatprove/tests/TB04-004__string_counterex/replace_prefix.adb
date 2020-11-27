with Ada.Strings.Fixed;

function Replace_Prefix
  (String_With_Prefix : String; Prefix, New_Prefix : String) return String
is
begin
   return New_Prefix & Ada.Strings.Fixed.Tail (String_With_Prefix, String_With_Prefix'Length - Prefix'Length);
end Replace_Prefix;
