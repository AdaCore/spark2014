package body Exp_Le_Last
   with SPARK_Mode
is

   procedure Foo (Offset : Natural)
   is
      Off : constant Natural := Offset mod Element_Type'Size;
   begin
      pragma Assert (Off < Element_Type'Size);
      pragma Assert ((Off + (Element_Type'Size - Off)) <= 62);
      pragma Assert (Off + (Element_Type'Size - Off) = Element_Type'Size);
      pragma Assert (2 ** (Off + (Element_Type'Size - Off)) = 2 ** Element_Type'Size);
   end Foo;

end Exp_Le_Last;
