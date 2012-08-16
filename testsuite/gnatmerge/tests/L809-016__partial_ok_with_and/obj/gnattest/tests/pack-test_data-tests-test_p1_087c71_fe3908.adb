--  function P1 (X : Integer) return Integer
--  Test Case "test case 1"

with Gnattest_Generated;

separate (Pack.Test_Data.Tests)
procedure Test_P1_087c71_fe3908 (Gnattest_T : in out Test) is
   pragma Unreferenced (Gnattest_T);
   function P1 (X : Integer) return Integer renames Wrap_Test_P1_087c71_fe3908;
begin
   AUnit.Assertions.Assert
     (P1 (3) = 4,
      "Test failed.");
end Test_P1_087c71_fe3908;
