procedure Main with SPARK_Mode is

   type Int_Cst_Acc is access constant Integer;

   procedure My_Lemma (X : Int_Cst_Acc) with
     Ghost,
     Global => null,
     Always_Terminates,
     Import;

   procedure Use_My_Lemma (X : Int_Cst_Acc) is
   begin
      My_Lemma (X);
   end Use_My_Lemma;

begin
   null;
end Main;
