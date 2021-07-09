procedure Bad_Access with SPARK_Mode is
   type Int_Ptr is access all Integer;

   function F (X : Int_Ptr) return Boolean with Import;

   procedure P (X, Y : Int_Ptr) with Import;

   X : Int_Ptr := new Integer'(10);
   Z : Integer := X.all'Access.all;
   W : Integer := Int_Ptr'(X.all'Access).all;
   B : Boolean := F (X.all'Access);
begin
   P (X.all'Access, X.all'Access);
end Bad_Access;
