package body Lots_Of_Tests
  with Refined_State => (State  => (A, B),
                         State2 => (C, D),
                         State3 => null)
is
   A, B, C, D : Integer := 0;

   procedure No_Contracts (X : out Integer) is
   begin
      X := G1 + A - C;
   end No_Contracts;

   procedure Internal_User_Of_No_Contracts_OK (X : out Integer) is
   begin
      No_Contracts (X);
   end Internal_User_Of_No_Contracts_OK;

   procedure Internal_User_Of_No_Contracts_BAD (X : out Integer) is
   begin
      No_Contracts (X);
   end Internal_User_Of_No_Contracts_BAD;

   procedure G (X, Y : in out Integer) is
   begin
      X := X + Y;
      Y := G1 + A;
   end G;

   procedure Internal_User_Of_G_OK (X, Y : in out Integer)
     with Refined_Global => (Input => (G1, A))
   is
   begin
      G (X, Y);
   end Internal_User_Of_G_OK;

   procedure Internal_User_Of_G_BAD (X, Y : in out Integer)
     with Refined_Global => (Input => (G1, B))
   is
   begin
      G (X, Y);
   end Internal_User_Of_G_BAD;

   procedure Dep (X : Integer; Y : out Integer) is
   begin
      Y  := X + C;
      G2 := A;
   end Dep;

   procedure Internal_User_Of_Dep_OK (X : Integer; Y : out Integer)
     with Refined_Global => (Input  => (A, C),
                             Output => G2)
   is
   begin
      Dep (X, Y);
   end Internal_User_Of_Dep_OK;

   procedure Internal_User_Of_Dep_BAD (X : Integer; Y : out Integer) is
   begin
      Dep (X, Y);
   end Internal_User_Of_Dep_BAD;

   procedure G_D (X : out Integer) is
   begin
      X  := A;
      G2 := G1;
   end G_D;

   procedure Internal_User_Of_G_D_OK (X : out Integer)
     with Refined_Global  => (Input  => (A, G1),
                              Output => G2),
          Refined_Depends => (G2 => G1,
                              X  => A)
   is
   begin
      G_D (X);
   end Internal_User_Of_G_D_OK;

   procedure Internal_User_Of_G_D_BAD (X : out Integer)
     with Refined_Depends => (G2 => G1,
                              X  => B)
   is
   begin
      G_D (X);
   end Internal_User_Of_G_D_BAD;

   procedure RG
     with Refined_Global => (Input  => (G1, A),
                             Output => (C, D))
   is
   begin
      C := G1;
      D := A;
   end RG;

   procedure Internal_User_Of_RG_OK
     with Refined_Depends => ((C, D) => (G1, A))
   is
   begin
      RG;
   end Internal_User_Of_RG_OK;

   procedure Internal_User_Of_RG_BAD
     with Refined_Global  => (Input  => (G1, A, B),
                              Output => (C, D))
   is
   begin
      RG;
   end Internal_User_Of_RG_BAD;

   procedure RG_D
     with Refined_Global => (Proof_In => A,
                             Input    => C,
                             Output   => G1)
   is
   begin
      pragma Assert (A > 5);

      G1 := C;
   end RG_D;

   procedure Internal_User_Of_RG_D_OK
     with Refined_Depends => (G1 => C)
   is
   begin
      RG_D;
   end Internal_User_Of_RG_D_OK;

   procedure Internal_User_Of_RG_D_BAD
     with Refined_Depends => (G1 => D)
   is
   begin
      RG_D;
   end Internal_User_Of_RG_D_BAD;

   procedure RD
     with Refined_Depends => (G1 => A,
                              A  => C)
   is
   begin
      G1 := A;
      A  := C;
   end RD;

   procedure Internal_User_Of_RD_OK
     with Refined_Global => (Input  => C,
                             In_Out => A,
                             Output => G1)
   is
   begin
      RD;
   end Internal_User_Of_RD_OK;

   procedure Internal_User_Of_RD_BAD
     with Refined_Global => (In_Out => (A, C),
                             Output => G1)
   is
   begin
      RD;
   end Internal_User_Of_RD_BAD;

   procedure G_RD
     with Refined_Depends => (A => (A, C),
                              B => C)
   is
   begin
      A := A + C;
      B := C;
   end G_RD;

   procedure Internal_User_Of_G_RD_OK
     with Refined_Global => (Input  => C,
                             In_Out => A,
                             Output => B)
   is
   begin
      G_RD;
   end Internal_User_Of_G_RD_OK;

   procedure Internal_User_Of_G_RD_BAD
     with Refined_Depends => ((A, B) => C)
   is
   begin
      G_RD;
   end Internal_User_Of_G_RD_BAD;

   procedure RG_RD
     with Refined_Global  => (In_Out => (G1, A)),
          Refined_Depends => (A      =>+ G1,
                              G1     => null)
   is
   begin
      A  := A + G1;
      G1 := 5;
   end RG_RD;

   procedure Internal_User_Of_RG_RD_OK
     with Refined_Global  => (In_Out => (G1, A))
   is
   begin
      RG_RD;
   end Internal_User_Of_RG_RD_OK;

   procedure Internal_User_Of_RG_RD_BAD
     with Refined_Global  => (In_Out => (G1, B))
   is
   begin
      RG_RD;
   end Internal_User_Of_RG_RD_BAD;
end Lots_Of_Tests;
