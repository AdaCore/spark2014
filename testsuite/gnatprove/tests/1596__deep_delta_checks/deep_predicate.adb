pragma Extensions_Allowed (All_Extensions);

procedure Deep_Predicate with SPARK_Mode is
   type Inner is array (1 .. 2) of Integer;
   type Checked is record
      F : Integer;
   end record with Predicate => F >= 0;
   type Rec is record
      A : Checked;
      B : Inner;
   end record;
   type Outer is array (1 .. 2) of Rec;
   X : constant Outer := (others => (A => (F => 0), B => (others => 0)));

   --  The nested array update must not restrict the predicate check on A

   Y : constant Outer :=
     (X with delta (2).A.F => -1, (1).B (1) => 1); -- @PREDICATE_CHECK:FAIL
begin
   null;
end Deep_Predicate;
