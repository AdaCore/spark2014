procedure Loop_Borrow is
   type Int_Acc is access Integer;
   X : Int_Acc := new Integer'(1);
begin
   loop
      pragma Loop_Invariant (X /= null and then X.all = 1);
      declare
         Y : access Integer := X;
      begin
         Y.all := 2;
      end;
      pragma Assert (X.all = 1);  --  @ASSERT:FAIL
   end loop;
end Loop_Borrow;
