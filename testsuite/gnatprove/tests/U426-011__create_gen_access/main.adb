procedure Main with SPARK_Mode is
   type Big_Rec is record
      F : Integer := 1;
   end record;

   type Rec_Arr is array (1 .. 100) of Big_Rec;
   Data : aliased Rec_Arr;

   type Rec_Arr_Acc is access all Rec_Arr;
   Data_Ptr : constant Rec_Arr_Acc := Data'Access;

   package Nested with
     Initial_Condition => Data_Ptr = null
   is
      type Big_Rec is record
         F : Integer := 1;
      end record;

      type Rec_Arr is array (1 .. 100) of Big_Rec;
      type Rec_Arr_Acc is access all Rec_Arr;

      Data_Ptr : Rec_Arr_Acc;
   end Nested;
   use Nested;

   Nested_Data : aliased Nested.Rec_Arr;
   Tmp_Ptr     : Nested.Rec_Arr_Acc := Nested_Data'Access;

   procedure Init_Nested_Data with
     Pre  => Nested.Data_Ptr = null and Tmp_Ptr /= null,
     Post => Nested.Data_Ptr /= null and Tmp_Ptr = null
     and Nested.Data_Ptr.all = Tmp_Ptr.all'Old
   is
   begin
      Nested.Data_Ptr := Tmp_Ptr;
      Tmp_Ptr := null;
   end Init_Nested_Data;

begin
   Init_Nested_Data;
end Main;
