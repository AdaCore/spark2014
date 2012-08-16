--  function P1 (X : Integer) return Integer
--  Test Case "test case 1"

with Gnattest_Generated;

separate (Pack.Test_Data.Tests)
procedure Test_P1_087c71_f47982 (Gnattest_T : in out Test) is
   pragma Unreferenced (Gnattest_T);
   function P1 (X : Integer) return Integer renames Wrap_Test_P1_087c71_f47982;
begin
   AUnit.Assertions.Assert
     (P1 (1) = 2,
      "Test failed.");
end Test_P1_087c71_f47982;
