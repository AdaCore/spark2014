--  procedure Execute (Read : Reader)
--  Test Case "Seqway moving forward"

with Gnattest_Generated;
with Reader; use Reader;

separate (Segway.Test_Data.Tests)
procedure Test_Execute_d996c3_82e7f0 (Gnattest_T : in out Test) is
   pragma Unreferenced (Gnattest_T);
   procedure Execute (Read : Reader) renames Wrap_Test_Execute_d996c3_82e7f0;
begin
   Segway.State := Forward;
   Segway.Speed := 10;
   Execute (Common_Reader'Access);
end Test_Execute_d996c3_82e7f0;
