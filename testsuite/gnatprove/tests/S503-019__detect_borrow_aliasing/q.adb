procedure Q with
  SPARK_Mode
is
   type Int_Ptr is access Integer;
   type Int_Ptr_Ptr is access Int_Ptr;
   X_Ptr : Int_Ptr_Ptr;

   procedure Proc (Y : Int_Ptr)
       with Global => (In_Out => X_Ptr)
   is
   begin
       X_Ptr.all.all := Y.all + 1;
       Y.all := X_Ptr.all.all + 1;
   end Proc;

begin
   X_Ptr := new Int_Ptr;
   X_Ptr.all := new Integer'(1);
   Proc (X_Ptr.all);  --  illegal
end Q;
