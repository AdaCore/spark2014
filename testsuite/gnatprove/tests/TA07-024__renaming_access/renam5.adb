procedure Renam5 is
   type Int_Acc is access Integer;
   X : Int_Acc := new Integer'(1);

   generic
      Int_Obj : in out Integer;
   procedure G with Global => null;

   procedure G is null;

   procedure I is new G (X.all);
begin
   null;
end;
