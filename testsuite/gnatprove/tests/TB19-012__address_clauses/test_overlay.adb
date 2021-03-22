procedure Test_Overlay (C : Integer; D : in out Integer) with SPARK_Mode is
   X : constant Integer := 15;
   Y : Integer with Address => X'Address; --rejected
   Z : Integer with Address => C'Address; --rejected
   W : Integer with Address => D'Address; --ok

   type Int_Acc is access constant Integer;
   function Init return not null Int_Acc with Import;
   S : Int_Acc := Init;
   V : Integer with Address => S.all'Address; --rejected
   U : constant Integer with Import, Address => S.all'Address; --ok
begin
   null;
end Test_Overlay;
