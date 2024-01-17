package P_Bad with Spark_Mode is
   type Chars_Ptr is access String;

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
   pragma SPARK_Mode (Off);

   Null_Ptr : constant Chars_Ptr := null;
end P_Bad;
