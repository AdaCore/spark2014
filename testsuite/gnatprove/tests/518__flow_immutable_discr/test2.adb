procedure Test2 with SPARK_Mode is

   type Set (Capacity : Natural := 0) is record
      Length : Natural;
   end record;

   type Big_Empty_Set is record
      S : Set (0);
   end record;

   procedure P_1 (Big : in out Big_Empty_Set) is
      C : Natural range 0 .. Big.S.Capacity := 0;
      --  Inner discriminant is effectively immutable; frontend expands the
      --  upper bound to 0, which has no variable inputs.
      --
      --  It is OK to ACCEPT it.
   begin
      Big.S := (Capacity => 0, Length => 0);
   end P_1;

   type Outer_Empty_Set (Outer_Capacity : Natural := 0) is record
      S : Set (Outer_Capacity);
   end record;

   procedure P_2 (Outer : in out Outer_Empty_Set) is
      C : Natural range 0 .. Outer.S.Capacity := 0;
      --  Inner discriminant is mutable, at least in Ada; frontend expands the
      --  upper bounds to an internal constant initialized with the original
      --  upper bound expression, which is kind of mutable.
      --
      --  It is OK to REJECT this.
   begin
      Outer := (Outer_Capacity => 1, S => (Capacity => 1, Length => 0));
   end P_2;

begin
   null;
end Test2;
