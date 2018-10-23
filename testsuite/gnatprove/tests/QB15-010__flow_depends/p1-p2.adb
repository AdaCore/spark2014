package body P1.P2 with Refined_State => (State2 => X2) is
   X2 : Integer := 0;
   function F return Integer is (X2) with Refined_Depends => (F'Result => State1);
   --  The refined depends contract is fine, even though it could be more precise,
   --  i.e. it could be "F'Result => X2".
end;
