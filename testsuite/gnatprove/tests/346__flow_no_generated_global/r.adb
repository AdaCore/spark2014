package body R is

   --  Non-null refinement requires non-null Refined_Global

   package body A with Refined_State => (State => X) is
      X : Integer := 0;
      function F return Integer is (X);
   end;

   --  Null refinement requires null Refined_Global

   package body B with Refined_State => (State => null) is
      function F return Integer is (0);
   end;
end;
