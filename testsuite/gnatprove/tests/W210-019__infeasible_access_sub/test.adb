procedure Test (G : Integer) with SPARK_Mode is
   C : constant Integer := 10;

   package OK is

      --  Check that the precondition is taken into account for the feasibility check

      type F is access function (X : Integer) return Positive with --@FEASIBLE_POST:PASS
        Pre  => X >= C,
        Post => F'Result in C .. X;

      --  Check that the value of constants is taken into account for the feasibility check

      type G is access function return Positive with --@FEASIBLE_POST:PASS
        Post => G'Result > C;
   end OK;

   package Bad is

      --  Possibly infeasible post

      type F is access function (X : Integer) return Positive with --@FEASIBLE_POST:FAIL
        Post => F'Result in C .. X;

      type My_Pos is new Integer range C .. G;

      --  Possibly infeasible implicit post

      type G is access function return My_Pos; --@FEASIBLE_POST:FAIL
   end Bad;
begin
   null;
end;
