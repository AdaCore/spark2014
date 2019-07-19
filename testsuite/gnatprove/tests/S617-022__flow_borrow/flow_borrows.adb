procedure Flow_Borrows with SPARK_Mode is
   type Int_Ptr is access Integer;
   type Two_Ptrs is record
      F , G : Int_Ptr;
   end record;

   XF : Int_Ptr := new Integer'(5);
   XG : Int_Ptr := new Integer'(5);
   X  : Two_Ptrs := (F => XF, G => XG);

   procedure Update_X_F (I : Integer) with
     Global => (In_Out => X),  --  warning: "X" is not modified, could be INPUT
     Pre    => X.F /= null,
     Post   => X.F.all = I
   is
      Y : access Integer := X.F;-- warning: initialization of "Y" has no effect
      Z : access Integer := X.G;-- warning: initialization of "Y" has no effect
   begin
      Y.all := I;--  warning: unused assignment
      Z.all := I;--  warning: unused assignment
   end Update_X_F;

begin
   declare
      Y : access Integer := X.F;
   begin
      pragma Assert (Y.all = 5);
   end;
   pragma Assert (X.F.all = 5);
end Flow_Borrows;
