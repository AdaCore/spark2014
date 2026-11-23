pragma Extensions_Allowed (All_Extensions);

procedure Deep_Leak with SPARK_Mode is
   type Int_Acc is access Integer;
   type Integers is array (1 .. 2) of Integer;
   type Pointers is array (1 .. 2) of Int_Acc;
   type Rec is record
      A : Integers;
      B : Pointers;
   end record;
   type Outer is array (1 .. 2) of Rec;
   X : Outer := (others => (A => (others => 0), B => (others => null)));
begin
   X (2).B (1) := new Integer'(1);
   declare
      Y : Outer :=
        (X with delta
           (1).A (1) => 1,
           (2).B (1) => null); -- @RESOURCE_LEAK:FAIL
   begin
      Y := (Y with delta (2).B (1) => null); -- @RESOURCE_LEAK:PASS
      pragma Assert (Y (1).A (1) = 1); -- @ASSERT:PASS
      pragma Assert (Y (2).B (1) = null); -- @ASSERT:PASS
   end;
end Deep_Leak;
