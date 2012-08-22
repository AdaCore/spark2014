--  procedure Execute (Read : Reader)
--  Test Case "Segway standing still"

with Gnattest_Generated;
with Reader; use Reader;

separate (Segway.Test_Data.Tests)
procedure Test_Execute_d996c3_987a21 (Gnattest_T : in out Test) is
   pragma Unreferenced (Gnattest_T);
   procedure Execute (Read : Reader) renames Wrap_Test_Execute_d996c3_987a21;
begin
   Segway.State := Still;
   Segway.Speed := 0;
   Execute (Common_Reader'Access);
end Test_Execute_d996c3_987a21;
