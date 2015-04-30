package Refined_Post_Illegal_3
  with SPARK_Mode
is
   --  TU: 7. When a subprogram or entry with a Refined Postcondition
   --  is called, the Refined Postcondition is evaluated immediately
   --  before the evaluation of the postcondition or, if there is no
   --  postcondition, immediately before the point at which a
   --  postcondition would have been evaluated. If the Refined
   --  Postcondition evaluates to False, then the exception
   --  Assertion.Assertion_Error is raised.  Otherwise, the
   --  postcondition is then evaluated and checked as described in the
   --  Ada RM.
   procedure P1 (Par : out Integer)
     with Post => Par = 1;


   procedure P2 (Par : out Integer)
     with Post => Par = 1;
end Refined_Post_Illegal_3;
