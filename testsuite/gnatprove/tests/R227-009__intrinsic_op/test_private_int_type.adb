with Private_Int_Type; use Private_Int_Type;

procedure Test_Private_Int_Type with SPARK_Mode is
   X : Boolean;
begin
   if My_Zero <= My_One then
      X := My_Zero > My_One;
      pragma Assert (X); --@ASSERT:FAIL
   end if;
end Test_Private_Int_Type;
