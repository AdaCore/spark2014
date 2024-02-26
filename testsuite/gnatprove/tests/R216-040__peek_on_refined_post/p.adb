package body P is
   package Nested is
      function F1 return Integer with Post => F1'Result >= 0;
      function F2 return Integer with Post => F2'Result >= 0;
      function F3 return Integer with Post => F3'Result >= 0;
   end;

   package body Nested is
      function Zero return Integer is (0) with Pre => True;
      --  Helper function with explicit Pre (which should prevent inlining)

      function F1 return Integer with Refined_Post => F1'Result = 0 is
      begin
         return Zero;
      end F1;

      function F2 return Integer is (Zero);

      function F3 return Integer is (Zero) with Refined_Post => F3'Result = 0;
   end;

   pragma Assert (Nested.F1 = 0); -- @ASSERT:FAIL
   --  This can only be proved if the Refined_Post is visible (but it is not)
   pragma Assert (Nested.F2 = 0); -- @ASSERT:FAIL
   --  This can only be proved if the expression function body is visible (but it is not)
   pragma Assert (Nested.F3 = 0); -- @ASSERT:FAIL
   --  Both together

end;
