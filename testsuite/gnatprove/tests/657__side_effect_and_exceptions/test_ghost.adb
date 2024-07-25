procedure Test_Ghost with SPARK_Mode is
   function F return Integer with
     Import,
     Global => null,
     Always_Terminates,
     Side_Effects,
     Exceptional_Cases => (Program_Error => True);

   procedure P with
     Import,
     Ghost,
     Global => null,
     Always_Terminates,
     Exceptional_Cases => (Program_Error => True);

   type Int_Acc is access Integer;

   X : Int_Acc := new Integer'(4);
   Y : Int_Acc;
   I : Integer with Ghost;
begin
   begin
      Y := X;
      X := Y;
      I := F;  -- @RAISE:FAIL
      P;       -- @RAISE:FAIL
   exception
      when Program_Error => pragma Assert (False);
   end;

   Y := X;
end Test_Ghost;
