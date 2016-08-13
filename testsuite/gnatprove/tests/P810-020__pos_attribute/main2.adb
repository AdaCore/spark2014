with Interfaces;  use Interfaces;
with Ada.Text_IO; use Ada.Text_IO;

procedure main2 with SPARK_Mode is
   type Some_Record is
       record
          c1 : Unsigned_8 := 0;
          c2 : Unsigned_8 := 0;
       end record;
   for Some_Record use
       record
          c1 at 0 range 0 .. 7;  --  representation clauses added
          c2 at 1 range 0 .. 7;
       end record;
   for Some_Record'Size use 16;
   foo : Some_Record;

   off_c1 : constant Integer := foo.c1'Position;
   off_c2 : constant Integer := foo.c2'Position;
begin
   pragma Assert (off_c1 < 10000);
   pragma Assert (off_c2 = 0);
   Put_Line ("Pos c1=" & Integer'Image (off_c1)); -- stdout: 0
   Put_Line ("Pos c2=" & Integer'Image (off_c2)); -- stdout: 1
end main2;
