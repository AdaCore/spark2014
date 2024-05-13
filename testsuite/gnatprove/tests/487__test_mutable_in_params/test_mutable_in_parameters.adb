with Unchecked_Deallocation;

procedure Test_Mutable_In_Parameters with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   package C_Strings with Always_Terminates is
      type Chars_Ptr is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      Null_Ptr : constant Chars_Ptr with
        Annotate => (GNATprove, Ownership, "Reclaimed_Value");

      function New_String (Str : String) return Chars_Ptr with
        Global => null,
        Volatile_Function,
        Import,
        Post => New_String'Result /= Null_Ptr
        and then Strlen (New_String'Result) = Str'Length
        and then Value (New_String'Result) = Str;

      procedure Free (Item : in out Chars_Ptr) with
        Global => null,
        Import,
        Post => Item = Null_Ptr;

      function Value (Item : Chars_Ptr) return String with
        Global => null,
        Import,
        Pre => Item /= Null_Ptr,
        Post => Value'Result'First = 1
        and then Value'Result'Length = Strlen (Item);

      function Value
        (Item   : Chars_Ptr;
         Length : Natural) return String
      with
        Global => null,
        Import,
        Pre => Item /= Null_Ptr and then Length /= 0,
        Post => Value'Result'First = 1
        and then Value'Result'Length = Natural'Min (Length, Strlen (Item))
        and then (for all I in 1 .. Value'Result'Length =>
                    Value'Result (I) = Value (Item) (I));

      function Strlen (Item : Chars_Ptr) return Natural with
        Global => null,
        Import,
        Pre => Item /= Null_Ptr;

      procedure Update
        (Item   : Chars_Ptr;
         Offset : Natural;
         Str    : String;
         Check  : Boolean := True)
      with
        Global => null,
        Import,
        Pre =>
            Item /= Null_Ptr
            and then Str'Length <= Natural'Last - Offset
            and then Str'Length + Offset <= Strlen (Item),
        Post =>
            Item /= Null_Ptr
            and then Strlen (Item) = Strlen (Item)'Old
            and then (for all I in 1 .. Strlen (Item) =>
                        (if Str'Length > 0
                           and then I in Offset + 1 .. Offset + Str'Length
                         then Value (Item) (I) = Str (I - Offset - 1 + Str'First)
                         else Value (Item) (I) = Value (Item)'Old (I)));
      pragma Annotate (GNATprove, Mutable_In_Parameters, Chars_Ptr);
   private
      pragma SPARK_Mode (Off);
      type Chars_Ptr is access all Character;

      Null_Ptr : constant Chars_Ptr := null;
   end C_Strings;

   procedure Test_C_Strings is
      use C_Strings;
      X : Chars_Ptr := Null_Ptr;
      Y : Chars_Ptr := New_String ("foo_foo");
   begin
      pragma Assert (Strlen (Y) = 7);
      pragma Assert (Value (Y) = "foo_foo");
      X := New_String ("bar");
      Update (Y, 4, Value (X));
      Free (X);
      pragma Assert (Strlen (Y) = 7);
      pragma Assert (Value (Y) = "foo_bar");
      Free (Y);
   end Test_C_Strings;

   package Mock_Up is
      type Chars_Ptr is private;

      Null_Ptr : constant Chars_Ptr;

      function New_String (Str : String) return Chars_Ptr with
        Global => null,
        Post => New_String'Result /= Null_Ptr
        and then Strlen (New_String'Result) = Str'Length
        and then Value (New_String'Result) = Str;

      procedure Free (Item : in out Chars_Ptr) with
        Global => null,
        Post => Item = Null_Ptr;

      function Value (Item : Chars_Ptr) return String with
        Global => null,
        Pre => Item /= Null_Ptr,
        Post => Value'Result'First = 1
        and then Value'Result'Length = Strlen (Item);

      function Value
        (Item   : Chars_Ptr;
         Length : Natural) return String
      with
        Global => null,
        Pre => Item /= Null_Ptr and then Length /= 0,
        Post => Value'Result'First = 1
        and then Value'Result'Length = Natural'Min (Length, Strlen (Item))
        and then (for all I in 1 .. Value'Result'Length =>
                    Value'Result (I) = Value (Item) (I));

      function Strlen (Item : Chars_Ptr) return Natural with
        Global => null,
        Pre => Item /= Null_Ptr;

      procedure Update
        (Item   : Chars_Ptr;
         Offset : Natural;
         Str    : String;
         Check  : Boolean := True)
      with
        Global => null,
        Pre =>
            Item /= Null_Ptr
            and then Str'Length <= Natural'Last - Offset
            and then Str'Length + Offset <= Strlen (Item),
        Post =>
            Item /= Null_Ptr
            and then Strlen (Item) = Strlen (Item)'Old
            and then (for all I in 1 .. Strlen (Item) =>
                        (if Str'Length > 0
                         and then I in Offset + 1 .. Offset + Str'Length
                         then Value (Item) (I) = Str (I - Offset - 1 + Str'First)
                         else Value (Item) (I) = Value (Item)'Old (I)));
      pragma Annotate (GNATprove, Mutable_In_Parameters, Chars_Ptr);
   private
      type Chars_Ptr is access String with
        Predicate => Chars_Ptr = null or else Chars_Ptr'First = 1;

      Null_Ptr : constant Chars_Ptr := null;
   end Mock_Up;

   package body Mock_Up is

      function New_String (Str : String) return Chars_Ptr is
         Value : String (1 .. Str'Length) := Str;
      begin
         return new String'(Value);
      end New_String;

      procedure Dealloc is new Unchecked_Deallocation (String, Chars_Ptr);

      procedure Free (Item : in out Chars_Ptr) is
      begin
         Dealloc (Item);
      end Free;

      function Value (Item : Chars_Ptr) return String is (Item.all);

      function Value
        (Item   : Chars_Ptr;
         Length : Natural) return String
      is
      begin
         if Length > Item'Length then
            return Item.all;
         else
            return Item.all (1 .. Length);
         end if;
      end Value;

      function Strlen (Item : Chars_Ptr) return Natural is (Item'Length);

      procedure Update
        (Item   : Chars_Ptr;
         Offset : Natural;
         Str    : String;
         Check  : Boolean := True)
      is
      begin
         if Str'Length /= 0 then
            Item.all (1 + Offset .. Offset + Str'Length) := Str;
         end if;
      end Update;
   end Mock_Up;

   procedure Test_Mock_Up is
      use Mock_Up;
      X : Chars_Ptr := Null_Ptr;
      Y : Chars_Ptr := New_String ("foo_foo");
   begin
      pragma Assert (Strlen (Y) = 7);
      pragma Assert (Value (Y) = "foo_foo");
      X := New_String ("bar");
      Update (Y, 4, Value (X));
      Free (X);
      pragma Assert (Strlen (Y) = 7);
      pragma Assert (Value (Y) = "foo_bar");
      Free (Y);
   end Test_Mock_Up;
begin
   null;
end Test_Mutable_In_Parameters;
