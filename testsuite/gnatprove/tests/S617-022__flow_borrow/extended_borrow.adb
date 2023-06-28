procedure Extended_Borrow with SPARK_Mode is
   type Int_Ptr is access Integer;

   XF : Int_Ptr := new Integer'(5);

   function Update_X_F (I : Integer) return Integer with
     Pre => XF /= null
   is
      Y : access Integer := XF;
   begin
      Y.all := I;
      return Dummy : Integer := 123 do
         null;
      end return;
   end Update_X_F;

begin
   null;
end;
