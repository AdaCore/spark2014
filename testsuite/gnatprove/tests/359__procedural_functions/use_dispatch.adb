with Dispatch; use Dispatch;

procedure Use_Dispatch with SPARK_Mode is
   X1 : T1;
   X2 : T2;
   X1C : T1'Class := X1;
   X2C : T1'Class := X2;
   B : Boolean;
begin
   B := X1.F;
   pragma Assert (B);
   B := X2.F;
   pragma Assert (B);
   X1C.P (B);
   pragma Assert (B);
   X2C.P (B);
   pragma Assert (B);
   B := X1C.FF;
   pragma Assert (B);
   B := X2C.FF;
   pragma Assert (B);
   B := X1C.F;
   pragma Assert (B);
   B := X2C.F;
   pragma Assert (B);
   X1C := T1'Class(X1);
   B := X1C.F;
   pragma Assert (B);
   X2C := T2'Class(X2);
   B := X2C.F;
   pragma Assert (B);
end Use_Dispatch;
