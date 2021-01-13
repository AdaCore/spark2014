procedure Main with SPARK_Mode is
   type Int_Ptr is access Integer;
   function Id (X : access Int_Ptr) return access Int_Ptr with Import;
   type Int_Ptr_Ptr is access Int_Ptr;

   procedure Do_Something (X : out Int_Ptr) with Import;

   X : Int_Ptr := new Integer'(20);
   Y : Int_Ptr_Ptr := new Int_Ptr'(X);
   Z : Int_Ptr := Y.all;
begin
   Id (Y).all := Z;
   Do_Something (Id (Y).all);
end;
