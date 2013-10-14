with Refined_Depends_Legal.Pr_Child;

package body Refined_Depends_Legal
  with Refined_State => (S       => (A, B),
                         S2      => (C, D),
                         S3      => (Refined_Depends_Legal.Pr_Child.Pr_State,
                                     Refined_Depends_Legal.Pr_Child.Pr_Var),
                         S_Null  => null,
                         S_Null2 => null)
is
   A, B, C, D : Integer := 1;

   procedure P1 (Par1 : in     Integer;
                 Par2 :    out Integer;
                 Par3 : in out Integer)
     with Refined_Global  => (Input  => A,
                              Output => (C, D)),
          Refined_Depends => (Par2 => (Par1, A),
                              Par3 => Par3,
                              C    => A,
                              D    => Par3)
   is
   begin
      Par2 := Par1 + A;
      Par3 := Par3 + 1;
      C    := A;
      D    := Par3;
   end P1;

   procedure P2
     with Refined_Global  => (Input  => Refined_Depends_Legal.Pr_Child.Pr_Var,
                              In_Out =>
                                Refined_Depends_Legal.Pr_Child.Pr_State),
          Refined_Depends => (Refined_Depends_Legal.Pr_Child.Pr_State =>+
                                Refined_Depends_Legal.Pr_Child.Pr_Var)
   is
   begin
      Refined_Depends_Legal.Pr_Child.Update_Pr_State;
   end P2;
end Refined_Depends_Legal;
