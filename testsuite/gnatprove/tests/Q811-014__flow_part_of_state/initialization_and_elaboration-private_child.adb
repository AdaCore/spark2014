package body Initialization_And_Elaboration.Private_Child
  with Refined_State => (State => S)
is
   S : Integer; -- intentionally uninitialized

   procedure Init (I : Integer)
     with Refined_Global => (Output => S) is
   begin
     S := I;
   end;

   function Get return Integer is (S)
     with Refined_Global => S;
end Initialization_And_Elaboration.Private_Child;
