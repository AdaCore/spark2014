procedure Unint_Alloc (C : Positive) with SPARK_Mode is
   type My_Array is array (Positive range <>) of Integer with
     Predicate => My_Array'First = 1,
     Default_Component_Value => 0;
   type A_Ptr is access My_Array;
   type My_Rec is record
      R : A_Ptr;
   end record;
   X : My_Rec;
begin
   X.R := new My_Array (1 .. C);
end Unint_Alloc;
