with Ada.Text_IO; use Ada.Text_IO;

procedure Pointertest3
 with SPARK_Mode => On
is
  type Word is not null access String;
  type Dictionary is array (Positive range <>) of Word;
  My_Dictionary_1 : constant Word := new String'("Aword");
  My_Dictionary_2 : constant Word := new String'("Bword");  --<<< this is line 8.
  My_Dictionary : Dictionary(1..2) := (My_Dictionary_1, My_Dictionary_2);
begin
  -- My_Dictionary (1) := new String'("foo");  -- Think this causes a "memory leak" of the old string.

  Put_Line("Minimal program");
end Pointertest3;
