package Refined_Post_Illegal_2
  with SPARK_Mode
is
   procedure P1 (Par : out Integer)
     --  TU: 4. Logically, the Refined Postcondition of a subprogram must imply
     --  its postcondition. This means that it is perfectly logical for the
     --  declaration not to have a postcondition (which in its absence
     --  defaults to True) but for the body or body stub to have a
     --  Refined Postcondition.
     with Post => Par >= 10;


   function F1 return Boolean;

   procedure Calls_F1;


   procedure P2 (Par1, Par2 : Integer ; Par3 : out Integer)
     --  TU: 8. If a subprogram has both a Refined_Postcondition
     --  aspect and a Postcondition aspect, then the proof obligation
     --  associated with the Postcondition aspect is discharged in two
     --  steps. The success of the Refined_Postcondition run-time
     --  check must be proven as usual. It must also be shown that
     --  the precondition (or, in the case of a dispatching operation,
     --  the class-wide precondition) and the refined postcondition
     --  together imply the postcondition of the subprogram, that is:
     --
     --  (Precondition and Refined Postcondition) -> Postcondition
     --
     --  [Note that this step does not depend on the statements or
     --  declarations within the subprogram.]
     with Pre  => Par1 > 10,
          Post => Par3 > 101;
end Refined_Post_Illegal_2;
