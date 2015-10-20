with Interfaces.C; use Interfaces.C;

package Strings_Interface is
   pragma Preelaborate;

   type Char_Array_Access is access all char_array;
   for Char_Array_Access'Size use 64;

   pragma No_Strict_Aliasing (Char_Array_Access);
   --  Since this type is used for external interfacing, with the pointer
   --  coming from who knows where, it seems a good idea to turn off any
   --  strict aliasing assumptions for this type.

   type Chars_Ptr is private;
   pragma Preelaborable_Initialization (Chars_Ptr);

   type Chars_Ptr_Array is array (size_t range <>) of aliased Chars_Ptr;

   Null_Ptr : constant Chars_Ptr;

   function To_Chars_Ptr
     (Item      : Char_Array_Access;
      Nul_Check : Boolean := False) return Chars_Ptr;

   Terminator_Error : exception;
private
   type Chars_Ptr is access all Character;
   for Chars_Ptr'Size use 64;

   pragma No_Strict_Aliasing (Chars_Ptr);
   --  Since this type is used for external interfacing, with the pointer
   --  coming from who knows where, it seems a good idea to turn off any
   --  strict aliasing assumptions for this type.

   Null_Ptr : constant Chars_Ptr := null;
end Strings_Interface;
