procedure Test_Access_Conv with SPARK_Mode is
   type Rec (X : Boolean) is record
      F : Integer;
   end record;

   type Rec_Acc is access Rec;
   subtype S is Rec_Acc (True);

   procedure Incr (X : S) with Import;

   X : Rec_Acc := new Rec'(True, 12);
begin
   Incr (X);
end Test_Access_Conv;
