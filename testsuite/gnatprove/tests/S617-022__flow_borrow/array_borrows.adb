procedure Array_Borrows with SPARK_Mode is
    type Int_Ptr is access Integer;
    type Two_Ptrs is array (Boolean) of Int_Ptr;

    XF : Int_Ptr := new Integer'(5);
    XG : Int_Ptr := new Integer'(5);
    X  : Two_Ptrs := (True => XF, False => XG);

   procedure Update_X_F (I : Integer; J : Boolean) with
     Global => (In_Out => X),  --  warning: "X" is not modified, could be INPUT
     Pre    => X (True) /= null,
     Post   => X (True).all = I
   is
      Y : access Integer := X (J);-- warning: initialization of "Y" has no effect
   begin
      Y.all := I;--  warning: unused assignment
   end Update_X_F;

begin
    declare
       Y : access Integer := X (True);
    begin
       pragma Assert (Y.all = 5);
    end;
    pragma Assert (X (True).all = 5);
end Array_Borrows;
