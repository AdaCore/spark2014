package Dyn_Pred with SPARK_Mode is
  type Non_Zero_Type is private;

  function Is_Positive (The_Limit : Non_Zero_Type) return Boolean;

  subtype Positive_Subtype is Non_Zero_Type
    with Dynamic_Predicate => Is_Positive (Positive_Subtype);

  One : constant Positive_Subtype;

private
  type Non_Zero_Type is record
     Val : Integer;
  end record with Dynamic_Predicate => Non_Zero_Type.Val /= 0;

  function Is_Positive (The_Limit : Non_Zero_Type) return Boolean
    is (The_Limit.Val > 0);

  One : constant Positive_Subtype := (Val => 1);
end;
