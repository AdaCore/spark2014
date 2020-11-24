package body Refined_Depends_Examples
  with SPARK_Mode,
       Refined_State => (State => (A, B))
is
   A : Integer;  --  The constituents of State
   B : Integer;

   procedure P1_1 (I : in Integer)
     with Refined_Global  => (In_Out => A,
                              Output => B),
          Refined_Depends => (A => I,  --  A and B are constituents of State and
                                       --  both are outputs.
		              B => A)  --  A is dependent on I but A is also an
                                       --  input and B depends on A. Hence the
                                       --  Depends => (State =>+ I).
   is
   begin
      B := A;
      A := I;
   end P1_1;

   procedure P1_2 (I : in Integer)
     with Refined_Global  => (Output => A),
          Refined_Depends => (A => I)  --  One but not all of the constituents
                                       --  of State is updated hence the
                                       --  Depends => (State =>+ I)
   is
   begin
      A := I;
   end P1_2;

   procedure P1_3 (Result : out Integer)
     with Refined_Global  => (Input => B),
          Refined_Depends => (Result => B)  --  Not all of the constituents of
                                            --  State are read but none of them
                                            --  are updated, hence
                                            --  Depends => (Result => State)
   is
   begin
      Result := B;
   end P1_3;

   procedure P1_4 (I : in Integer)
     with Refined_Global  => (Output => (A, B)),
          Refined_Depends => ((A, B) => I)  --  The constituents of State are not
                                            --  inputs but all constituents of
                                            --  State are updated, hence,
                                            --  Depends => (State => I)
   is
   begin
      A := I;
      B := I;
   end P1_4;

end Refined_Depends_Examples;
