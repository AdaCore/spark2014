with SPARK.C.Strings;
with Ada.Text_IO;
procedure Foo with SPARK_Mode => On is
    package ICS renames SPARK.C.Strings;
    Chr : ICS.chars_ptr := ICS.New_String("Char");
begin
    Ada.Text_IO.Put_Line("The length of " & ICS.Value(Chr) & " is "
        & ICS.Strlen(Chr)'Image & ", and that's OK");
end Foo;
