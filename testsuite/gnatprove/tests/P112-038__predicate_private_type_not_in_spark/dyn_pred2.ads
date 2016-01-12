package Dyn_Pred2 with SPARK_Mode is
  type Rec_Type is private;
  type Non_Zero_Type is private;

  function Is_Positive (The_Limit : Rec_Type) return Boolean;

  subtype Positive_Subtype is Non_Zero_Type
    with Dynamic_Predicate => Is_Positive (Positive_Subtype);
private
  pragma SPARK_Mode (Off);
  type Rec_Type is record
     Val : Integer;
  end record;

  type Non_Zero_Type is new Rec_Type
    with Dynamic_Predicate => Non_Zero_Type.Val /= 0;

  function Is_Positive (The_Limit : Rec_Type) return Boolean
    is (The_Limit.Val > 0);
end;
