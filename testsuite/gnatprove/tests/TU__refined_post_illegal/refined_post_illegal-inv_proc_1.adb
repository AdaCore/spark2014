separate (Refined_Post_Illegal)
procedure Inv_Proc_1 (X, Y : in out Integer)
  with SPARK_Mode,
       Refined_Post => X = Y'Old - 1 and Y = Y'Old + 1
  --  The Refined_Post contract cannot be here. It should
  --  have been placed right after the "is separate".
is
begin
   X := Y - 1;
   Y := Y + 1;
end Inv_Proc_1;
