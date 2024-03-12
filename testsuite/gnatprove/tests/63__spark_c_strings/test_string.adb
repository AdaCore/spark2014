with Interfaces.C;         use Interfaces.C;
with SPARK.C.Strings;      use SPARK.C.Strings;

procedure Test_String with SPARK_Mode is

   procedure Test_Strings is
      X : Chars_Ptr := Null_Ptr;
      Y : Chars_Ptr := New_String ("foo_foo");
   begin
      pragma Assert (Strlen (Y) = 7);
      pragma Assert (Value (Y) = String'("foo_foo"));
      X := New_String ("bar");
      Update (Y, 4, String'(Value (X, Strlen (X))));
      Free (X);
      pragma Assert (Strlen (Y) = 7);
      pragma Assert (Value (Y) = String'("foo_bar"));
      Free (Y);
   end Test_Strings;

   procedure Test_Char_Array is
      X : Chars_Ptr := Null_Ptr;
      Y : Chars_Ptr := New_Char_Array ("foo_foo");
   begin
      pragma Assert (Strlen (Y) = 7);
      pragma Assert (Value (Y) = Char_Array'("foo_foo") & nul);
      X := New_Char_Array ("bar");
      Update (Y, 4, Char_Array'(Value (X, Strlen (X))));
      Free (X);
      pragma Assert (Strlen (Y) = 7);
      pragma Assert (Value (Y) = Char_Array'("foo_bar") & nul);
      Free (Y);
   end Test_Char_Array;

begin
   Test_Strings;
   Test_Char_Array;
end Test_String;
