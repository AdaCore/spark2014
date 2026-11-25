pragma Extensions_Allowed (All_Extensions);

procedure Deep_Paths (D : Integer) with SPARK_Mode is
   type Inner is array (1 .. 2) of Integer;
   type Rec is record
      A, B : Inner;
   end record;
   type Outer is array (1 .. 2) of Rec;
   X : constant Outer := (others => (others => (others => 0)));
   Y : constant Outer :=
     (X with delta (1).A (1) => 1, (2).B (1) => 2);
begin
   pragma Assert (Y (1).A (1) = 1); -- @ASSERT:PASS
   pragma Assert (Y (2).B (1) = 2); -- @ASSERT:PASS
   pragma Assert (D /= 0); -- @ASSERT:FAIL
end Deep_Paths;
