package body P1.P2 with Refined_State => (State2 => X2) is
   X2 : Integer := 0;
   function F return Integer is (X2);
   --  The generated Refined_Global should be "X2"

   function Test return Integer is (F) with Global => X2;
   --  The global contract is fine; it should be the same as the generated
   --  Refined_Global of function F.
end;
