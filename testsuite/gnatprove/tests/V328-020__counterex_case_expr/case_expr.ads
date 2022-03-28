package Case_Expr is

  type Index is range 1 .. 5;

  type Index_Array is array (Index) of Index;

  type Number is (One, Two, Three, Four, Five);

  function Return_One return Index;

  function Case_Expr (N : Number) return Index;

  function Case_Expr_Range (N : Number) return Index;

  function Case_Expr_In_Case_Expr return Index;

  procedure Loop_Entry_In_Case_Expr;

end Case_Expr;
