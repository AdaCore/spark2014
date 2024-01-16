package C_Strings with
  SPARK_Mode,
  Always_Terminates
is
   type Chars_Ptr is private with
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   Null_Ptr : constant Chars_Ptr with
     Annotate => (GNATprove, Ownership, "Reclaimed_Value");

   function New_String (Str : String) return Chars_Ptr with
     Global => null,
     Volatile_Function,
     Post => New_String'Result /= Null_Ptr;

   procedure Free (Item : in out Chars_Ptr) with
     Global => null,
     Post => Item = Null_Ptr;
private
   pragma SPARK_Mode (Off);
   type Chars_Ptr is access all Character;

   Null_Ptr : constant Chars_Ptr := null;
end C_Strings;
