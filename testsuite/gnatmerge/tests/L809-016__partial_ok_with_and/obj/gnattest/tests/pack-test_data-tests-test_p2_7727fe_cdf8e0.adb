--  function P2 (X : Integer) return Integer
--  Test Case "test case 2"

with Gnattest_Generated;

separate (Pack.Test_Data.Tests)
procedure Test_P2_7727fe_cdf8e0 (Gnattest_T : in out Test) is
   pragma Unreferenced (Gnattest_T);
   function P2 (X : Integer) return Integer renames Wrap_Test_P2_7727fe_cdf8e0;
begin
   AUnit.Assertions.Assert
     (P2 (1) = 3,
      "Test failed.");
end Test_P2_7727fe_cdf8e0;
