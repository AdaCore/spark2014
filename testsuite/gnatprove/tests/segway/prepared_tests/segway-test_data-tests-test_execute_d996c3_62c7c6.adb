--  procedure Execute (Read : Reader)
--  Test Case "Segway moving backward"

with Gnattest_Generated;
with Reader; use Reader;

separate (Segway.Test_Data.Tests)
procedure Test_Execute_d996c3_62c7c6 (Gnattest_T : in out Test) is
   pragma Unreferenced (Gnattest_T);
   procedure Execute (Read : Reader) renames Wrap_Test_Execute_d996c3_62c7c6;
begin
   Segway.State := Backward;
   Segway.Speed := -10;
   Execute (Common_Reader'Access);
end Test_Execute_d996c3_62c7c6;
