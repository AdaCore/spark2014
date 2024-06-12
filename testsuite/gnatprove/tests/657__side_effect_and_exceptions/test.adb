procedure Test with SPARK_Mode is
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
      I := F;
      X := Y;
   exception
      when Program_Error => null;
   end;

   Y := X;
end Test;
