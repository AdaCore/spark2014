procedure P4 (X : out Integer) is

   package Nested
     with Initializes => Used
   is
      Used : Integer;

      function F return Integer;
   end Nested;

   package body Nested is
      function F return Integer is (Used);
   begin
      Used := 0;
   end Nested;

begin
   X := Nested.F;
end P4;
