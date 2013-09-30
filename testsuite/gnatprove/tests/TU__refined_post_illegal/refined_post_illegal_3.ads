package Refined_Post_Illegal_3
  with SPARK_Mode
is
   --  TU: 7. When a subprogram with a Refined Postcondition is called; first
   --  the subprogram is evaluated. The Refined Postcondition is evaluated
   --  immediately before the evaluation of the postcondition or, if there is
   --  no postcondition, immediately before the point at which a
   --  postcondition would have been evaluated. If the Refined Postcondition
   --  evaluates to True then the postcondition is evaluated as described in
   --  the Ada RM. If either the Refined Postcondition or the postcondition
   --  do not evaluate to True then the exception Assertions.Assertion_Error
   --  is raised.
   procedure P1 (Par : out Integer)
     with Post => Par = 1;


   procedure P2 (Par : out Integer)
     with Post => Par = 1;
end Refined_Post_Illegal_3;
