package Refined_Post_Illegal_2
  with SPARK_Mode
is
   procedure P1 (Par : out Integer)
     --  TU: 4. [Logically, the Refined Postcondition of a subprogram must
     --  imply its postcondition. This means that it is perfectly logical for
     --  the declaration not to have a postcondition (which in its absence
     --  defaults to True) but for the body or body stub to have a Refined
     --  Postcondition. It also means that a caller who sees the Refined
     --  Postcondition of a subprogram will always be able to prove at least as
     --  much about the results of the call as if the usual precondition were
     --  used instead.]
     with Post => Par >= 10;

   function F1 return Boolean;

   procedure Calls_F1;

   procedure P2 (Par1, Par2 : Integer ; Par3 : out Integer)
     --  TU: 7. If a subprogram has both a Refined_Post aspect and a Post
     --  (and/or Post'Class) aspect, then the verification condition associated
     --  with postcondition checking is discharged in two steps.
     --
     --  First, the success of the Refined_Post run-time check must be proven
     --  as usual (i.e., just like any other run-time check).
     --
     --  Next, an additional proof obligation is generated which relates the
     --  Refined_Post to to the Post (and Post'Class) aspects of the subprogram
     --  according to a "wrapper" model. Imagine two subprograms with the same
     --  parameter profile and Global and Depends aspects, but with different
     --  postconditions P1 and P2 (neither of these two subprograms has a
     --  Refined_Post aspect).  Suppose further that the first subprogram is a
     --  "wrapper" for the second; that is, its implementation consists of
     --  nothing but a call to the second subprogram (for functions, the call
     --  would occur in a return statement). Consider the proof obligation
     --  generated for the postcondition check of that "wrapper" subprogram;
     --  roughly speaking, it is a check that P1 is implied by P2. In that
     --  sense of the word "implied", a verification condition is generated
     --  that any Post/Post'Class condition for a subprogram is implied by its
     --  Refined_Post condition. In particular, knowledge about the internals
     --  of the subprogram that was available in proving the Refined_Post
     --  condition is not available in proving this implication (just as, in
     --  the "wrapper" illustration, the internal details of the second
     --  subprogram are not available in proving the postcondition of the
     --  first).
     with Pre  => Par1 > 10,
          Post => Par3 > 101;
end Refined_Post_Illegal_2;
