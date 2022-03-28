package body Case_Expr is

  ----------------
  -- Return_One --
  ----------------

  function Return_One return Index is (1);

  ---------------
  -- Case_Expr --
  ---------------

  function Case_Expr (N : Number) return Index is
    I : Index;
  begin
    I := (case N is
            when One => Return_One,
            when Two => 2,
            when Three => 3,
            when Four => 4,
            when Five => 5);
    pragma Assert (I = 1);   --  @ASSERT:FAIL @COUNTEREXAMPLE
    return I;
  end Case_Expr;

  ---------------------
  -- Case_Expr_Range --
  ---------------------

  function Case_Expr_Range (N : Number) return Index is
    I : Index;
  begin
    I := (case N is
            when One => Return_One,
            when Two => 2,
            when Three .. Five => 3);
    pragma Assert (I = 3);   --  @ASSERT:FAIL @COUNTEREXAMPLE
    return I;
  end Case_Expr_Range;

  ----------------------------
  -- Case_Expr_In_Case_Expr --
  ----------------------------

  function Case_Expr_In_Case_Expr return Index is
    I : Index;
  begin
    I := (case Return_One is
            when (case One is
                    when One => 1 + 1 - 1,
                    when Two .. Five => 5) => 3 - 4 + 2,
            when others => 5);
    pragma Assert (I = 4);   --  @ASSERT:FAIL @COUNTEREXAMPLE
    return I;
  end Case_Expr_In_Case_Expr;

  -----------------------------
  -- Loop_Entry_In_Case_Expr --
  -----------------------------

  procedure Loop_Entry_In_Case_Expr is
    A : Index_Array := (others => 1);
  begin
    for J in A'Range loop
      A(J) := A(J) + 1;
      pragma Assert ((case A'Loop_Entry(J) is
                        when 1 => False,   --  @ASSERT:FAIL @COUNTEREXAMPLE
                        when others => False));
    end loop;
  end Loop_Entry_In_Case_Expr;

end Case_Expr;
