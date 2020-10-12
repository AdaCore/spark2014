procedure Renam4 is
   type Int_Acc is access Integer;
   X : Int_Acc := new Integer'(1);

   generic
      Int_Obj : in out Integer;
   package G is
      Int : Integer renames Int_Obj;
   end G;

   package I is new G (X.all);
begin
   X := new Integer'(2);
   pragma Assert (I.Int = 2);  -- this assertion fails
end;
