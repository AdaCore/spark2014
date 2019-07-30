procedure Flow_Borrows with SPARK_Mode is
   type Int_Ptr is access Integer;
   type Two_Ptrs is record
      F : Int_Ptr;
   end record;

   XF : Int_Ptr := new Integer'(5);
   X  : Two_Ptrs := (F => XF);

   procedure Update_X_F (I : Integer) with
     Global => (In_Out => X),
     Pre    => X.F /= null,
     Post   => X.F.all = I
   is
      Y : access Integer := Int_Ptr'(X.F);
   begin
      null;
   end Update_X_F;

begin
   null;
end Flow_Borrows;
