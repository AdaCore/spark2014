pragma Extensions_Allowed (All_Extensions);
with Interfaces; use Interfaces;

procedure Foo with SPARK_Mode is
   function Id (X : Unsigned_8) return Unsigned_8 is (X);
   type My_String is array (Unsigned_8 range <>) of character;
   C : My_String (Id (0) .. 255) with External_Initialization => "foo.txt";
   function F (S : My_String) return My_String is (S);
begin
   pragma Assert (F (C)'First = 0);
   pragma Assert (F (C)'Length = 256);
end Foo;
