with SPARK.C.Strings;
with SPARK.C.Constant_Strings;
with Ext; use Ext;
procedure Main with SPARK_Mode is

   procedure Test_New_String is
      use type SPARK.C.Strings.Chars_Ptr;
      X, Y : SPARK.C.Strings.Chars_Ptr :=  SPARK.C.Strings.New_String ("foo");
   begin
      pragma Assert (X = Y); --  ASSERT:FAIL
   end Test_New_String;

   procedure Test_New_Char_Array is
      use type SPARK.C.Strings.Chars_Ptr;
      X, Y : SPARK.C.Strings.Chars_Ptr :=  SPARK.C.Strings.New_Char_Array ("foo");
   begin
      pragma Assert (X = Y); --  ASSERT:FAIL
   end Test_New_Char_Array;

   procedure Test_To_Chars_Ptr is
      use type SPARK.C.Constant_Strings.Chars_Ptr;
      X : SPARK.C.Constant_Strings.Chars_Ptr := SPARK.C.Constant_Strings.To_Chars_Ptr
        (SPARK.C.Constant_Strings.Const_Char_Array_Access'(S1'Access));
      Y : SPARK.C.Constant_Strings.Chars_Ptr := SPARK.C.Constant_Strings.To_Chars_Ptr
        (SPARK.C.Constant_Strings.Const_Char_Array_Access'(S2'Access));
   begin
      pragma Assert (X = Y); --  ASSERT:FAIL
   end Test_To_Chars_Ptr;


begin
   null;
end Main;
