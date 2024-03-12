pragma Assertion_Policy (Ignore);

with Interfaces.C;         use Interfaces.C;
with Interfaces.C.Strings;
with SPARK.C.Strings;
with System.Parameters;

package C_Constant_Strings with SPARK_Mode, Always_Terminates is
   pragma Unevaluated_Use_Of_Old (Allow);

   type const_char_array_access is access constant char_array;
   for const_char_array_access'Size use System.Parameters.ptr_bits;

   pragma No_Strict_Aliasing (const_char_array_access);
   --  Since this type is used for external interfacing, with the pointer
   --  coming from who knows where, it seems a good idea to turn off any
   --  strict aliasing assumptions for this type.

   type chars_ptr is private with
     Default_Initial_Condition => Is_Null (Chars_Ptr);
   pragma Preelaborable_Initialization (chars_ptr);

   Null_Ptr : constant chars_ptr;

   --  We should start the copy here

   function Is_Null (Item : chars_ptr) return Boolean with
     Ghost,
     Post => Is_Null'Result = (Item = Null_Ptr);

   function Is_Nul_Terminated_Ghost (Item : String) return Boolean renames
     SPARK.C.Strings.Is_Nul_Terminated_Ghost;

   function C_Length_Ghost (Item : String) return Natural renames
     SPARK.C.Strings.C_Length_Ghost;

   --  Non SPARK primitives, should be used with care

   function To_Chars_Ptr
     (Item      : Interfaces.C.Strings.char_array_access;
      Nul_Check : Boolean := False) return chars_ptr
   with
     SPARK_Mode => Off;  --  To_Chars_Ptr'Result is aliased with Item

   function To_Chars_Ptr
     (Item : Interfaces.C.Strings.chars_ptr) return chars_ptr
   with
     SPARK_Mode => Off;
   --  To_Chars_Ptr'Result is aliased with Interfaces.C.Strings.C_Memory

   function From_Chars_Ptr
     (Item : chars_ptr) return Interfaces.C.Strings.chars_ptr
   with
     SPARK_Mode => Off;  --  Item is aliased with Interfaces.C.Strings.C_Memory

   function New_Char_Array (Chars : char_array) return chars_ptr with
     SPARK_Mode => Off;  --  Allocated memory might not be reclaimed

   function New_String (Str : String) return chars_ptr with
     SPARK_Mode => Off;  --  Allocated memory might not be reclaimed

   procedure Free (Item : in out chars_ptr) with
     SPARK_Mode => Off;
   --  Because of potential aliases, reclamation cannot be done safely

   --  SPARK primitives

   function To_Chars_Ptr
     (Item      : const_char_array_access;
      Nul_Check : Boolean := False) return chars_ptr
   with
     Volatile_Function,
     --  The value of To_Chars_Ptr'Result depends on the address of Item

     Pre            => Item = null or else Is_Nul_Terminated (Item.all),
     Contract_Cases =>
       (Item = null => To_Chars_Ptr'Result = Null_Ptr,
        others      => To_Chars_Ptr'Result /= Null_Ptr
        and then Strlen (To_Chars_Ptr'Result) = C_Length_Ghost (Item.all)
        --  Strlen returns the number of elements before the first occurrence
        --  of nul in Item.all.

        and then
          (for all I in 0 .. Strlen (To_Chars_Ptr'Result) =>
             Value (To_Chars_Ptr'Result) (I) = Item (Item'First + I))),
        --  Value returns the prefix of Item.all up to and including the first
        --  occurrence of nul.

     Global => null;

   function Value (Item : chars_ptr) return char_array with
     Pre    => Item /= Null_Ptr,
     Post   => Value'Result'First = 0
       and then Value'Result'Last = Strlen (Item)
       and then Value'Result (Strlen (Item)) = nul
       and then (for all I in 0 .. Strlen (Item) =>
                   (if I < Strlen (Item) then Value'Result (I) /= nul)),
     Global => null;
   --  Value returns the prefix of the value pointed by Item up to and
   --  including the first occurrence of nul.

   function Value
     (Item   : chars_ptr;
      Length : size_t) return char_array
   with
     Pre    => Item /= Null_Ptr and then Length /= 0,
     Post   => Value'Result'First = 0
       and then Value'Result'Last = size_t'Min (Length - 1, Strlen (Item))
       and then (for all I in 0 .. size_t'(Value'Result'Length - 1) =>
                   Value'Result (I) = char_array'(Value (Item)) (I)),
     Global => null;
   --  Value returns the longest prefix of Value (Item) containing at most
   --  Length elements.

   function Value (Item : chars_ptr) return String with
     Pre    => Item /= Null_Ptr
       and then Strlen (Item) <= size_t (Natural'Last),
     Post   => Value'Result'First = 1
       and then Value'Result'Length = Strlen (Item)
       and then (for all I in Value'Result'Range =>
                   Value'Result (I) /= To_Ada (nul))
       and then (for all I in Value'Result'Range =>
                   Value'Result (I) = To_Ada (Value (Item) (size_t (I - 1)))),
     Global => null;
   --  Value returns the prefix of the value pointed by Item up to but
   --  excluding the first occurrence of nul.

   function Value
     (Item   : chars_ptr;
      Length : size_t) return String
   with
     Pre    => Item /= Null_Ptr and then Length /= 0
       and then (Strlen (Item) <= size_t (Natural'Last)
                 or else Length <= size_t (Natural'Last)),
     Post   => Value'Result'First = 1
       and then Value'Result'Length = size_t'Min (Length, Strlen (Item))
       and then (for all I in Value'Result'Range =>
                   Value'Result (I) = To_Ada (Value (Item) (size_t (I - 1))))
       and then
         (if Strlen (Item) <= size_t (Natural'Last)
          then (for all I in Value'Result'Range =>
                      Value'Result (I) = Value (Item) (I))),
     Global => null;
   --  Value returns the longest prefix of Value (Item) containing at most
   --  Length elements.

   function Strlen (Item : chars_ptr) return size_t with
     Pre    => Item /= Null_Ptr,
     Global => null;
   --  Strlen returns the number of elements before the first occurrence of nul
   --  in the value pointed by Item.

private
   type Chars_Ptr is access constant Char_Array with
     Predicate => Chars_Ptr = null
     or else Is_Nul_Terminated (Chars_Ptr.all);

   Null_Ptr : constant Chars_Ptr := null;

   function Is_Null (Item : chars_ptr) return Boolean is
     (Item = null);
end C_Constant_Strings;
