procedure Access_To_Record with SPARK_Mode is
   type My_Rec (X : Boolean) is null record;
   type My_Rec_Access is access My_Rec;
   subtype S is My_Rec_Access (True);

   X : My_Rec_Access := new My_Rec'(X => False);
   Y : S := X; --@DISCRIMINANT_CHECK:FAIL
begin
   null;
end Access_To_Record;
