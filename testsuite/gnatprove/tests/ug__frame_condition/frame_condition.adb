package body Frame_Condition with
  SPARK_Mode
is
   procedure Update_Arr (A : in out Arr; Idx : Index) is
   begin
      for J in A'First .. Idx loop
         A(J) := Integer(J);
      end loop;
   end Update_Arr;

   procedure Update_Rec (R : in out Rec) is
   begin
      for J in R.A'Range loop
         R.A(J) := Integer(J);
      end loop;
   end Update_Rec;

end Frame_Condition;
