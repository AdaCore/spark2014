package body Aggregates with SPARK_Mode is

   procedure Create_Arr (X : out Arr_T) is
   begin
      X := (1, 1);  --  @INVARIANT_CHECK:NONE
   end Create_Arr;

   procedure Update_Arr (X : in out Arr_T) is
   begin
      X := (X(2), X(1));  --  @INVARIANT_CHECK:NONE
   end Update_Arr;

   function Get_Arr (X : Arr_T) return Integer is (Integer (X(1)));

   procedure Create_Rec (X : out Rec_T) is
   begin
      X := (1, 1);  --  @INVARIANT_CHECK:NONE
   end Create_Rec;

   procedure Update_Rec (X : in out Rec_T) is
   begin
      X := (X.B, X.A);  --  @INVARIANT_CHECK:NONE
   end Update_Rec;

   function Get_Rec (X : Rec_T) return Integer is (Integer (X.A));

end Aggregates;
