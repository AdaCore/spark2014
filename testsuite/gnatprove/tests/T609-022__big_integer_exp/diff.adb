with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Diff is
   type S63 is range 0 .. 2**63 - 1;

   type U63 is mod 2**63 with
     Annotate => (GNATprove, No_Wrap_Around);


   function S_Exp_Gt0 (J : Natural) return Boolean with
     Pre => J in 0 .. 8
   is
      X : constant S63 := 2**J;
   begin
      pragma Assert (X > 0);
      return True;
   end S_Exp_Gt0;

   function U_Exp_Gt0 (J : Natural) return Boolean with
     Pre => J in 0 .. 8
    is
      X : constant U63 := 2**J;
   begin
      pragma Assert (X > 0);  --  failing assertion
      return True;
   end U_Exp_Gt0;

   function S_Exp_Const_Trans (J : Natural) return Boolean with
     Pre => J in 0 .. 8
    is
      Pow2_J  : constant S63 := 2**J;
   begin
      pragma Assert (Pow2_J = 2**J);
      pragma Assert (2**J > 0);
      pragma Assert (Pow2_J > 0);
      return True;
   end S_Exp_Const_Trans;

   function U_Exp_Const_Trans (J : Natural) return Boolean with
     Pre => J in 0 .. 8
    is
      Pow2_J  : constant U63 := 2**J;
   begin
      pragma Assert (Pow2_J = 2**J);
      pragma Assert (2**J > 0);
      pragma Assert (Pow2_J > 0);  --  failing assertion
      return True;
   end U_Exp_Const_Trans;


   pragma Warnings (Off, "no Global contract available for ""*""");

   package S_Conversions is new Signed_Conversions (S63);
   package U_Conversions is new Unsigned_Conversions (U63);

   function S_Exp_BI_Trans (J : Natural) return Boolean with
     Pre => J in 0 .. 8
    is
      Pow2_J  : constant S63 := 2**J;
      Y : constant S63 := Pow2_J / 2;
   begin
      pragma Assert (Y <= 2**J);
      pragma Assert (S_Conversions.To_Big_Integer (Y) <= To_Big_Integer (2)**J);
      return True;
   end S_Exp_BI_Trans;

   function U_Exp_BI_Trans (J : Natural) return Boolean with
     Pre => J in 0 .. 8
    is
      Pow2_J  : constant U63 := 2**J;
      Y : constant U63 := Pow2_J / 2;
   begin
      pragma Assert (Y <= 2**J);
      pragma Assert (U_Conversions.To_Big_Integer (Y) <= To_Big_Integer (2)**J);
      return True;
   end U_Exp_BI_Trans;
begin
   null;
end;
