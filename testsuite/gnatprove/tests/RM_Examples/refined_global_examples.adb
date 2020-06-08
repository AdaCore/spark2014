package body Refined_Global_Examples
  with SPARK_Mode,
       Refined_State => (S1 => (A, B),
                         S2 => (X, Y, Z))
is
   A : Integer := 1;  --  The constituents of S1
   B : Integer := 2;  --  Initialized as promised

   X, Y, Z : Integer; --  The constituents of S2
                      --  Not initialized

   procedure P1_1 (I : in Integer)
     with Refined_Global => (In_Out => A,  --  Refined onto constituents of S1
                             Output => B)  --  B is Output but A is In_Out and
                                           --  so Global S1 is also In_Out
   is
   begin
      B := A;
      A := I;
   end P1_1;

   procedure P1_2 (I : in Integer)
     with Refined_Global => (Output => A)  --  Not all of the constituents of
                                           --  S1 are updated and so the Global
                                           --  S1 must In_Out
   is
   begin
      A := I;
   end P1_2;

   procedure P1_3 (Result : out Integer)
     with Refined_Global => (Input => B)  --  Not all of the constituents of S1
                                          --  are read but none of them are
                                          --  updated so the Global S1 is Input
   is
   begin
      Result := B;
   end P1_3;

   procedure P1_4 (I : in Integer)
     with Refined_Global => (Output => (A, B))  --  The constituents of S1 are
                                                --  not read but they are all
                                                --  updated and so the mode
                                                --  selector of S1 is Output
   is
   begin
      A := I;
      B := A;
   end P1_4;

   procedure P2
     with Refined_Global => (Input  => V1, --  V1 has no constituents and is
                                           --  not subject to refinement.
                             Output => Z)  --  Only constituent Z of S2 is
                                           --  updated and so mode selector of
                                           --  Global S2 is In_Out.
   is
   begin
      Z := V1;
   end P2;

   procedure P3 (J : in Integer)
     --  No Refined_Global aspect here because V1 has no refinement.
   is
   begin
      V1 := J;
   end P3;

   procedure P4
     with Refined_Global => (Input  => (A, V1), --  The refinement of both S1
                                                --  and S2 are visible and
                             Output => (X, Y))  --  cannot be denoted here.
                                                --  Their constituents must be
                                                --  used instead.
   is
   begin
      X := V1;
      Y := A;
   end P4;
end Refined_Global_Examples;
