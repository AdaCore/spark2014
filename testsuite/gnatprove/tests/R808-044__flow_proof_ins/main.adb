procedure Main (X : Integer) with Global => null is

   function Proof return Integer is (0)
   with Global => (Proof_In => X), Pre => X = 0;

   procedure Proof
   with Global => (Proof_In => X), Pre => X = 0 is
   begin null; end;
   --  The above routines simply read X as part of their preconditions, thus X
   --  should become Proof_In for routines below where they are evaluated.

   function F_NOK return Integer with Global => (Input => X) is
      Y : Integer := Proof;
   begin
      return Y;
   end;
   function F_OK return Integer with Global => (Proof_In => X) is
      Y : Integer := Proof;
   begin
      return Y;
   end;

   procedure P_NOK with Global => (Input => X) is
   begin
      Proof;
   end;

   procedure P_OK with Global => (Proof_In => X) is
   begin
      Proof;
   end;

begin
   null;
end;
