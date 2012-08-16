--  function P4 (X : Integer) return Integer
--  Test Case "test case 4"

with Gnattest_Generated;

separate (Pack.Test_Data.Tests)
procedure Test_P4_0599a5_76a6c4 (Gnattest_T : in out Test) is
   pragma Unreferenced (Gnattest_T);
   function P4 (X : Integer) return Integer renames Wrap_Test_P4_0599a5_76a6c4;
begin
   AUnit.Assertions.Assert
     (P4 (0) = 4,
      "Test failed.");
end Test_P4_0599a5_76a6c4;
