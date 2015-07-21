package body Dynamic_Preds_RTE
  with SPARK_Mode
is
   procedure Create_Small_Pair (X : out Small_Pair; Y : Integer) is
   begin
      X.A := Y;
      X.B := Y;
   end Create_Small_Pair;

   function Add_Small_Pair (X : Small_Pair) return Integer is
   begin
      return X.A + X.B;
   end Add_Small_Pair;

   procedure Create_Small_Array (X : out Small_Array; Y : Integer) is
   begin
      X(1) := Y;
      X(2) := Y;
   end Create_Small_Array;

   function Add_Small_Array (X : Small_Array) return Integer is
   begin
      return X(1) + X(2);
   end Add_Small_Array;

   procedure Create_Ordered_Small_Pair (X : out Ordered_Small_Pair) is
   begin
      X := (1, 2);
   end Create_Ordered_Small_Pair;

   procedure Create_Ordered_Small_Array (X : out Ordered_Small_Array) is
   begin
      X := (1, 2);
   end Create_Ordered_Small_Array;

end Dynamic_Preds_RTE;
