procedure Test (G : Integer) with SPARK_Mode is
   C : constant Integer := 10;

   package OK is
      type Root is abstract tagged null record;

      --  Check that the precondition is taken into account for the feasibility check

      function F (O : Root; X : Integer) return Positive is abstract with --@FEASIBLE_POST:PASS
        Pre'Class  => X >= C,
        Post'Class => F'Result in C .. X;

      --  Check that the value of constants is taken into account for the feasibility check

      function G (O : Root) return Positive is abstract with --@FEASIBLE_POST:PASS
        Post'Class => G'Result > C;
   end OK;

   package Bad is
      type Root is abstract tagged null record;

      --  Possibly infeasible post

      function F (O : Root; X : Integer) return Positive is abstract with --@FEASIBLE_POST:FAIL
        Post'Class => F'Result in C .. X;

      type My_Pos is new Integer range C .. G;

      --  Possibly infeasible implicit post

      function G (O : Root) return My_Pos is abstract; --@FEASIBLE_POST:FAIL
   end Bad;
begin
   null;
end;
