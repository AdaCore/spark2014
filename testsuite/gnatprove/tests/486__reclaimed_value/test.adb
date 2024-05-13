
procedure Test with SPARK_Mode is

   package P is
      type Chars_Ptr is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      Null_Ptr : constant Chars_Ptr with
        Annotate => (GNATprove, Ownership, "Reclaimed_Value");

      function New_String (Str : String) return Chars_Ptr with
        Global => null,
        Volatile_Function,
        Import,
        Post => New_String'Result /= Null_Ptr;

      procedure Free (Item : in out Chars_Ptr) with
        Global => null,
        Import,
        Post => Item = Null_Ptr;
   private
      pragma SPARK_Mode (Off);
      type Chars_Ptr is access all Character;

      Null_Ptr : constant Chars_Ptr := null;
   end P;
   use P;

   W : Chars_Ptr; --  No memory leak, but it is not provable as Null_Ptr cannot be used in the DIC of Chars_Ptr
   X : Chars_Ptr := Null_Ptr; --  No memory leak, no move
   Y : Chars_Ptr := New_String ("foo"); --  No memory leak, Y is reclaimed
   Z : Chars_Ptr := New_String ("bar"); -- @RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
begin
   Free (Y);
end Test;
