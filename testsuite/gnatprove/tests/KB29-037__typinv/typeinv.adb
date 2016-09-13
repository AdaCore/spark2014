package body Typeinv is 

   function New_T ( X : Integer) return T is
   begin
      -- will fail when X is not even
      return T (X); -- @INVARIANT_CHECK:FAIL
   end New_T;

   procedure Divide (X : in out T) is
   begin
      -- will not fail, the invariant is not checked here
      X := X / 2;

      -- The invariant is checked at procedure exit on (in-)out parameters
      -- the invariant check will fail when X is not the
      -- double of an even number
   end Divide;
end Typeinv;
