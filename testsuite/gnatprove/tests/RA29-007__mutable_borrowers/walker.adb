procedure Walker with SPARK_Mode is
   type Int_Acc is access Integer;

   type Two_Acc is record
      Fst : Int_Acc;
      Snd : Int_Acc;
   end record;

   X : Two_Acc := (new Integer'(1), new Integer'(2));
begin
   declare
      Y : access Integer := X.Fst;
   begin
      Y.all := 3;
   end;
   pragma Assert (X.Fst.all = 1);
end Walker;
