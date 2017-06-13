with Pkg_B; use Pkg_B;

package body Pkg_A with Refined_State => (State => (G1, G2))
is

   pragma Warnings (Off, "analyzing unreferenced *");

   G1 : Boolean;
   G2 : Boolean;

   procedure Partial_Init_With_Global
   with Refined_Global => (Output => G1)
   is
   begin
      G1 := False;
   end Partial_Init_With_Global;

   procedure Partial_Init_Without_Global
   is
   begin
      G1 := False;
   end Partial_Init_Without_Global;

   --  All of the below should be correct and not issue warnings or errors

   procedure Test_G_G_G
   with Global => (In_Out => (G1, G2))
   is
   begin
      Case_G_G;
      Case_G_G;
   end Test_G_G_G;

   procedure Test_G_NG_G
   with Global => (In_Out => (G1, G2))
   is
   begin
      Case_G_NG;
      Case_G_NG;
   end Test_G_NG_G;

   procedure Test_NG_G_G
   with Global => (In_Out => (G1, G2))
   is
   begin
      Case_NG_G;
      Case_NG_G;
   end Test_NG_G_G;

   procedure Test_NG_NG_G
   with Global => (In_Out => (G1, G2))
   is
   begin
      Case_NG_NG;
      Case_NG_NG;
   end Test_NG_NG_G;

   procedure Test_G_G_NG
   is
   begin
      Case_G_G;
      Case_G_G;
   end Test_G_G_NG;

   procedure Test_G_NG_NG
   is
   begin
      Case_G_NG;
      Case_G_NG;
   end Test_G_NG_NG;

   procedure Test_NG_G_NG
   is
   begin
      Case_NG_G;
      Case_NG_G;
   end Test_NG_G_NG;

   procedure Test_NG_NG_NG
   is
   begin
      Case_NG_NG;
      Case_NG_NG;
   end Test_NG_NG_NG;

end Pkg_A;
