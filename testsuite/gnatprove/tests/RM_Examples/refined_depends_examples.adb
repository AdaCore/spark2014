package body Refined_Depends_Examples
  with SPARK_Mode,
       Refined_State => (S1 => (A, B),
                         S2 => (X, Y, Z))
is
   A : Integer := 1;  --  The constituents of S1
   B : Integer := 2;  --  Initialized as promised

   X, Y, Z : Integer; --  The constituents of S2
                      --  Not initialized

   procedure P1_1 (I : in Integer)
     with Refined_Global  => (In_Out => A,
                              Output => B),
          Refined_Depends => (A => I,  --  A and B are constituents of S1 and
                                       --  both are outputs.
		              B => A)  --  A is dependent on I but A is also an
                                       --  input and B depends on A. Hence the
                                       --  Depends => (S1 =>+ I).
   is
   begin
      B := A;
      A := I;
   end P1_1;

   procedure P1_2 (I : in Integer)
     with Refined_Global  => (Output => A),
          Refined_Depends => (A => I)  --  One but not all of the constituents
                                       --  of S1 is updated hence the
                                       --  Depends => (S1 =>+ I)
   is
   begin
      A := I;
   end P1_2;

   procedure P1_3 (Result : out Integer)
     with Refined_Global  => (Input => B),
          Refined_Depends => (Result => B)  --  Not all of the constituents of
                                            --  S1 are read but none of them
                                            --  are updated, hence
                                            --  Depends => (Result => S1)
   is
   begin
      Result := B;
   end P1_3;

   procedure P1_4 (I : in Integer)
     with Refined_Global  => (Output => (A, B)),
          Refined_Depends => ((A, B) => I)  --  The constituents of S1 are not
                                            --  inputs but all constituents of
                                            --  S1 are updated, hence,
                                            --  Depends => (S1 => I)
   is
   begin
      A := I;
      B := I;
   end P1_4;

   procedure P2
     with Refined_Global  => (Input  => V1,
                              Output => Z),
          Refined_Depends => (Z => V1)  --  Only constituent Z of S2 is an
                                        --  output. The other constituents of
                                        --  S2 are preserved, hence,
                                        --  Depends => (S2 =>+ V1);
   is
   begin
      Z := V1;
   end P2;

   procedure P3 (J : in Integer)
     -- No Refined_Depends aspect here because V1 has no refinement.
   is
   begin
      V1 := J;
   end P3;

   procedure P4
     with Refined_Global  => (Input  => (A, V1),
                              Output => (X, Y)),
          Refined_Depends => (X => V1, --  Only constituents X and Y of S2 are
                                       --  updated.
                              Y => A)  --  Z is not updated and so S2 must have
                                       --  a self-dependency. Constituent A of
                                       --  S1 is read and no constituent of S1
                                       --  is updated, hence,
                                       --  Depends => (S2 =>+ (S1, V1))
   is
   begin
      X := V1;
      Y := A;
   end P4;
end Refined_Depends_Examples;
