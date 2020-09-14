procedure Test_Image (X : Integer) with SPARK_Mode is
   S  : String := X'Image;
   WS : Wide_String := X'Wide_Image;
   WWS: Wide_Wide_String := X'Wide_Wide_Image;
begin
   null;
end Test_Image;
