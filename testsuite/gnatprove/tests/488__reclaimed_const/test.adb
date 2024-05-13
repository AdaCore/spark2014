procedure Test with SPARK_Mode is

   package P is
      type Chars_Ptr is private;

      Null_Ptr : constant Chars_Ptr;

      function New_String (Str : String) return Chars_Ptr with
        Global => null,
        Import,
        Post => New_String'Result /= Null_Ptr;

      procedure Free (Item : in out Chars_Ptr) with
        Global => null,
        Import,
        Post => Item = Null_Ptr;
   private
      type Chars_Ptr is access String;

      Null_Ptr : constant Chars_Ptr := null;
   end P;
   use P;

   C1 : constant Chars_Ptr := Null_Ptr; --  No memory leak, no move
   C2 : constant Chars_Ptr := C1; --  No memory leak, no move
begin
   null;
end Test;
