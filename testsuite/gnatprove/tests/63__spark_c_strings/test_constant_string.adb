with Interfaces.C;                  use Interfaces.C;
with SPARK.C.Constant_Strings;      use SPARK.C.Constant_Strings;
with String_Literals;               use String_Literals;

procedure Test_Constant_String with SPARK_Mode is

   procedure Test_Strings is
      X : Chars_Ptr := To_Chars_Ptr (const_char_array_access'(Bar'Access));
      Y : Chars_Ptr := To_Chars_Ptr (const_char_array_access'(Foo_Foo'Access));
   begin
      pragma Assert (Strlen (X) = 3);
      pragma Assert (Value (X) = String'("bar"));
      pragma Assert (Strlen (Y) = 7);
      pragma Assert (Value (Y) = String'("foo_foo"));
      pragma Assert (Value (Y, 3) = String'("foo"));
   end Test_Strings;

   procedure Test_Char_Array is
      X : Chars_Ptr := To_Chars_Ptr (const_char_array_access'(Bar'Access));
      Y : Chars_Ptr := To_Chars_Ptr (const_char_array_access'(Foo_Foo'Access));
   begin
      pragma Assert (Strlen (X) = 3);
      pragma Assert (Value (X) = Char_Array'("bar") & nul);
      pragma Assert (Strlen (Y) = 7);
      pragma Assert (Value (Y) = Char_Array'("foo_foo") & nul);
      pragma Assert (Value (Y, 3) = Char_Array'("foo"));
   end Test_Char_Array;

begin
   Test_Strings;
   Test_Char_Array;
end Test_Constant_String;
