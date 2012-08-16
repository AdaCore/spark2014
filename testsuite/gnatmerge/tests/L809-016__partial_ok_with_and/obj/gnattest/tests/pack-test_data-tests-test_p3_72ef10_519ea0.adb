--  function P3 (X : Integer) return Integer
--  Test Case "test case 3"

with Gnattest_Generated;

separate (Pack.Test_Data.Tests)
procedure Test_P3_72ef10_519ea0 (Gnattest_T : in out Test) is
   pragma Unreferenced (Gnattest_T);
   function P3 (X : Integer) return Integer renames Wrap_Test_P3_72ef10_519ea0;
begin
   AUnit.Assertions.Assert
     (Gnattest_Generated.Default_Assert_Value,
      "Test not implemented.");
end Test_P3_72ef10_519ea0;
