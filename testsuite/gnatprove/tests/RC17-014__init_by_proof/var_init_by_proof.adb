with Ada.Text_IO;
procedure Var_Init_By_Proof with SPARK_Mode is
   type My_Nat is new Integer range 10 .. 150 with
     Relaxed_Initialization;

   procedure P3 (X : out My_Nat); -- @INIT_BY_PROOF:FAIL

   procedure P1 (X : My_Nat) is
   begin
      pragma Assert (X'Initialized);
   end P1;

   procedure P2 (X : in out My_Nat) is
      Z : My_Nat;
   begin
      pragma Assert (not Z'Initialized); -- @ASSERT:FAIL
      pragma Assert (X'Initialized);
      P3 (X);
      X := Z; -- @INIT_BY_PROOF:FAIL
   end P2;

   procedure P3 (X : out My_Nat) is
   begin
      null;
   end P3;

   G : My_Nat;

   procedure P4 (X : out My_Nat) with
     Pre => X'Initialized
   is
   begin
      X := G; -- @INIT_BY_PROOF:FAIL
   end P4;

   X : My_Nat;
   Y : My_Nat;
   Z : My_Nat;
   W : My_Nat;
begin
   X := 13;
   Y := X;
   P4 (X); -- @PRECONDITION:FAIL

   P1 (X);
   P2 (Y);
   pragma Assert (Y'Initialized);
   P3 (Z);
   P2 (W); -- @INIT_BY_PROOF:FAIL
end Var_Init_By_Proof;
