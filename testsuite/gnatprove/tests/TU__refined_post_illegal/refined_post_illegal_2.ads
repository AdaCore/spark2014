package Refined_Post_Illegal_2
  with SPARK_Mode
is
   procedure P1 (Par : out Integer)
     --  TU: 4. Logically, the Refined Postcondition of a subprogram must imply
     --  its postcondition. This means that it is perfectly logical for the
     --  declaration not to have a postcondition (which in its absence
     --  defaults to True) but for the body or body stub to have a
     --  Refined Postcondition.
     with Post => Par >= 0;


   function F1 return Boolean;
   --  TU: 5. The default Refined_Post for an expression function, F, is
   --  F'Result = ``expression``, where ``expression`` is the expression
   --  defining the body of the function.


   procedure Calls_F1;


   procedure P2 (Par1, Par2 : Integer ; Par3 : out Integer)
     --  TU: 8. The precondition of a subprogram declaration and its Refined
     --  Postcondition together imply the postcondition of the declaration,
     --  that is:
     --  (Precondition and Refined Postcondition) -> Postcondition
     with Pre  => Par1 > 10,
          Post => Par3 > 101;
end Refined_Post_Illegal_2;
