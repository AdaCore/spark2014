package body Preds is

   procedure Create_Int_OK (X : out Int_OK) is
      Tmp : Int_OK;  --  @PREDICATE_CHECK:PASS
   begin
      X := Tmp;
   end Create_Int_OK;

   procedure Create_Int_Bad (X : out Int_Bad) is
      Tmp : Int_Bad;  --  @PREDICATE_CHECK:FAIL
   begin
      X := Tmp;
   end Create_Int_Bad;

   procedure Create_Sub_Int_OK (X : out Sub_Int_OK) is
      Tmp : Sub_Int_OK;  --  @PREDICATE_CHECK:PASS
   begin
      X := Tmp;
   end Create_Sub_Int_OK;

   procedure Create_Sub_Int_Bad (X : out Sub_Int_Bad) is
      Tmp : Sub_Int_Bad;  --  @PREDICATE_CHECK:FAIL
   begin
      X := Tmp;
   end Create_Sub_Int_Bad;

   procedure Create_Sub_Intp_OK (X : out Sub_Intp_OK) is
      Tmp : Sub_Intp_OK;  --  @PREDICATE_CHECK:PASS
   begin
      X := Tmp;
   end Create_Sub_Intp_OK;

   procedure Create_Sub_Intp_Bad (X : out Sub_Intp_Bad) is
      Tmp : Sub_Intp_Bad;  --  @PREDICATE_CHECK:FAIL
   begin
      X := Tmp;
   end Create_Sub_Intp_Bad;

   procedure Create_Arr_OK (X : out Arr_OK) is
      Tmp : Arr_OK;  --  @PREDICATE_CHECK:PASS
   begin
      X := Tmp;
   end Create_Arr_OK;

   procedure Create_Arr_Bad (X : out Arr_Bad) is
      Tmp : Arr_Bad;  --  @PREDICATE_CHECK:FAIL
   begin
      X := Tmp;
   end Create_Arr_Bad;

   procedure Create_Rec_OK (X : out Rec_OK) is
      Tmp : Rec_OK;  --  @PREDICATE_CHECK:PASS
   begin
      X := Tmp;
   end Create_Rec_OK;

   procedure Create_Rec_Bad (X : out Rec_Bad) is
      Tmp : Rec_Bad;  --  @PREDICATE_CHECK:FAIL
   begin
      X := Tmp;
   end Create_Rec_Bad;

   procedure Create_Rec_Wrap_OK (X : out Rec_Wrap_OK) is
      Tmp : Rec_Wrap_OK;
   begin
      X := Tmp;
   end Create_Rec_Wrap_OK;

   procedure Create_Rec_Wrap_Bad (X : out Rec_Wrap_Bad) is
      Tmp : Rec_Wrap_Bad;
   begin
      X := Tmp;
   end Create_Rec_Wrap_Bad;

end Preds;
