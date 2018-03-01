package body P is
   package Nested is
      function F return Integer with Post => F'Result >= 0;
   end;

   package body Nested is
      function Zero return Integer is (0) with Pre => True;
      --  Helper function with explicit Pre (which should prevent inlining)

      function F return Integer is (Zero) with Refined_Post => F'Result = 0;
   end;

   pragma Assert (Nested.F = 0); -- @ASSERT:FAIL
   --  This can only be proved if the Refined_Post is visible (but it is not)
end;
