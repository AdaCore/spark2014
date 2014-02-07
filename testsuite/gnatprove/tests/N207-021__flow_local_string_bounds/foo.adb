procedure Foo (A : Integer;
               B : out Integer;
               C : out Integer)
with Global => null,
     Depends => ((B, C) => A)
is
   Tmp_B : String          := Integer'Image (A);
   Tmp_C : constant String := Integer'Image (A);
begin
   B := Tmp_B'Length;
   C := Tmp_C'Length;
end Foo;
