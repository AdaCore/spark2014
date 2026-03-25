with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   type E is (AAA, BBB);

begin

   pragma Assert (E'Image (E'First) = "AAA");   -- @ASSERT:PASS

   Put_Line ("Done");

end;
