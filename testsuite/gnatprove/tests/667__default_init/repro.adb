procedure Repro
  with SPARK_Mode
is
   type String_Access is access String;
   Null_String_Access : constant String_Access := new String'("hello");

   type Unbounded_String is record
      Reference : not null String_Access := Null_String_Access;
      Last      : Natural                := 0;
   end record;

   function Get return Unbounded_String
     with Post => Get'Result.Reference.all = Null_String_Access.all'Old
   is
      Result : Unbounded_String;
   begin
      return Result;
   end;

   X : Unbounded_String := Get;
   Y : Unbounded_String := Get;
begin
   X.Reference.all := "world";
   pragma Assert (Y.Reference.all = "hello");
end;
