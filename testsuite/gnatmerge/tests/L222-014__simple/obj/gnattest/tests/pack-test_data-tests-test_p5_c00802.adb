--  procedure P5

with Gnattest_Generated;

separate (Pack.Test_Data.Tests)
procedure Test_P5_c00802 (Gnattest_T : in out Test) is
   pragma Unreferenced (Gnattest_T);
begin
   AUnit.Assertions.Assert
     (Gnattest_Generated.Default_Assert_Value,
      "Test not implemented.");
end Test_P5_c00802;
