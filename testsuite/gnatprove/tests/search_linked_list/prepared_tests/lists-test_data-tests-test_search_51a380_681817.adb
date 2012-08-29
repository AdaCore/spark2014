--  function Search (L : List) return Cursor
--  Test Case "some zero"

with Gnattest_Generated;

separate (Lists.Test_Data.Tests)
procedure Test_Search_51a380_681817 (Gnattest_T : in out Test) is
   pragma Unreferenced (Gnattest_T);
   function Search (L : List) return Cursor renames Wrap_Test_Search_51a380_681817;

   L : List (100);
   C : Cursor;
begin
   L.Append (1);
   L.Append (2);
   L.Append (3);
   L.Append (0);
   L.Append (8);
   C := Search(L);
end Test_Search_51a380_681817;
