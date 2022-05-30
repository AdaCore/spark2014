package body Arr_Not_Equal is

   function Empty (A : Arr) return Boolean is
      C : constant Arr (2 .. 1) := (others => 42);
      B : constant Boolean      := A /= C;
   begin
      pragma Assert (A /= C);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return B;
   end Empty;

   function All_Same_Values (A : Arr) return Boolean is
      C : constant Arr     := (1 => 1, 2 => 1, 3 => 1);
      B : constant Boolean := A /= C;
   begin
      pragma Assert (A /= C);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return B;
   end All_Same_Values;

   function All_Same_Others (A : Arr) return Boolean is
      C : constant Arr (1 .. 3) := (others => 1);
      B : constant Boolean      := A /= C;
   begin
      pragma Assert (A /= C);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return B;
   end All_Same_Others;

   function All_Diff_Values (A : Arr) return Boolean is
      C : constant Arr     := (1 => 1, 2 => 2, 3 => 3);
      B : constant Boolean := A /= C;
   begin
      pragma Assert (A /= C);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return B;
   end All_Diff_Values;

   function All_Diff_Others (A : Arr) return Boolean is
      C : constant Arr (1 .. 3) := (1 => 1, 3 => 3, others => 2);
      B : constant Boolean      := A /= C;
   begin
      pragma Assert (A /= C);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return B;
   end All_Diff_Others;

   function Mix (A : Arr) return Boolean is
      --  (1, 2, 3, 1, 4, 1, 5, 1, 2, 3, 1)
      C : constant Arr (1 .. 11) := (2  => 3,
                                    3  => 3,
                                    5  => 4,
                                    7  => 5,
                                    9  => 2,
                                    10 => 3,
                                    others => 1);
      B : constant Boolean := A /= C;
   begin
      pragma Assert (A /= C);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return B;
   end Mix;

end Arr_Not_Equal;
