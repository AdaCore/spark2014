procedure Test_OK with SPARK_Mode is
   function F return Integer with
     Import,
     Global => null,
     Always_Terminates,
     Side_Effects,
     Exceptional_Cases => (Program_Error => True);

   type Int_Acc is access Integer;

   X : Int_Acc := new Integer'(4);
   Y : Int_Acc;
   I : Integer;
begin
   begin
      Y := X;
      X := Y;
      I := F;
   exception
      when Program_Error => null;
   end;

   Y := X;
end Test_OK;
