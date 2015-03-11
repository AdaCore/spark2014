package body Foo
is

   type Disc_T (Valid : Boolean := False) is record
      F : Natural;
   end record;

   type Arr_T is array (Natural range <>) of Boolean;

   X : Natural;
   Y : Natural;
   Z : Disc_T;
   W : Arr_T (1 .. 10);

   --  Missing global: high/error
   procedure Test_SRM_6_1_4_Rule_12 (N : out Integer)
   with Global => X
   is
   begin
      N := X + Y;
   end Test_SRM_6_1_4_Rule_12;

   --  Unnecessary global: low
   procedure Test_SRM_6_1_4_Rule_13 (N : out Integer)
   with Global => (X, Y)
   is
   begin
      N := X;
   end Test_SRM_6_1_4_Rule_13;

   --  rule 14 says we can use abstract state, not very exciting

   --  correct modes

   --  in is only in: high/error
   procedure Test_SRM_6_1_4_Rule_15_A
   with Global => (X, Y)
   is
   begin
      X := X + 12;  -- in out
      Y := 12;      --    out
   end Test_SRM_6_1_4_Rule_15_A;

   --  out when not intput except for discriminant or attribute use
   --           and fully initialized
   procedure Test_SRM_6_1_4_Rule_15_B (N : out Natural;
                                       M : out Boolean;
                                       O : out Natural)
   with Global => (Output => (X, Y, Z, W))
   is
   begin
      N := X;      --  in
      Y := Y + 1;  --  in out

      M := Z.Valid;
      Z := (False, 0);

      O := W'Length;
      W := (others => False);
   end Test_SRM_6_1_4_Rule_15_B;

   --  inout are inout
   procedure Test_SRM_6_1_4_Rule_15_C (N : out Natural)
   with Global => (In_Out => (X, Y))
   is
   begin
      N := X;   -- in
      Y := 12;  -- out
   end Test_SRM_6_1_4_Rule_15_C;

   --  proof_in are proof_in
   procedure Test_SRM_6_1_4_Rule_16 (N : out Natural;
                                     M : out Natural)
   with Global => (Input => X,
                   Proof_In => Y)
   is
      Tmp1 : Natural;
      Tmp2 : Natural with Ghost;
   begin
      pragma Assert (X = 12);  -- should be proof_in
      N    := Y;               -- not allowed
      Tmp1 := Y;               -- not allowed
      Tmp2 := Y;               -- OK
      M    := Tmp1;            -- OK (in theory)
   end Test_SRM_6_1_4_Rule_16;

   --  can't test 17 yet

   --  can't test 18 yet

end Foo;
