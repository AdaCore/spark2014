with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   type E is (AAA, BBB);

begin

   --  This assertion does not hold by default. It would only hold if
   --  Discard_Names pragma/aspect = True. However, that pragma/aspect is not
   --  set in this example. Furthermore, it isn't even supported by GNATprove.
   --  So, GNATprove should detect the wrong assertion here.

   pragma Assert (E'Image (E'First) = " 0");   -- @ASSERT:FAIL

   Put_Line ("Should not be reached!");

end;
