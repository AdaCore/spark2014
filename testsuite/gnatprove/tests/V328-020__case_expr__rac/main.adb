with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

  type Index is range 1 .. 5;

  type Index_Array is array (Index) of Index;

  type Number is (One, Two, Three, Four, Five);

  function Return_One return Index;

  function Case_Expr (N : Number) return Index;

  function Case_Expr_Range (N : Number) return Index;

  function Case_Expr_In_Case_Expr return Index;

  procedure Loop_Entry_In_Case_Expr;

  --  Implementations

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
                        when 1      => True,
                        when others => False));
      Put_Line ("True");
    end loop;
  end Loop_Entry_In_Case_Expr;

begin

  Put_Line ("Case_Expr");
  Put_Line ("Expect 1:" & Index'Image (Case_Expr (One)));
  Put_Line ("Expect 2:" & Index'Image (Case_Expr (Two)));
  Put_Line ("Expect 3:" & Index'Image (Case_Expr (Three)));
  Put_Line ("Expect 4:" & Index'Image (Case_Expr (Four)));
  Put_Line ("Expect 5:" & Index'Image (Case_Expr (Five)));
  Put_Line ("");

  Put_Line ("Case_Expr_Range");
  Put_Line ("Expect 1:" & Index'Image (Case_Expr_Range (One)));
  Put_Line ("Expect 2:" & Index'Image (Case_Expr_Range (Two)));
  Put_Line ("Expect 3:" & Index'Image (Case_Expr_Range (Three)));
  Put_Line ("");

  Put_Line ("Case_Expr_In_Case_Expr");
  Put_Line ("Expect 1:" & Index'Image (Case_Expr_In_Case_Expr));
  Put_Line ("");

  Put_Line ("Loop_Entry_In_Case_Expr");
  Put_Line ("5 True:");
  Loop_Entry_In_Case_Expr;

end Main;
