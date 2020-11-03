procedure Test_Not_Null_Out with SPARK_Mode is
   type Empty is range 1 .. 0;
   type Empty_Acc is not null access Empty;
   procedure P (X : out Empty_Acc) with
     Pre => True
   is
   begin
      pragma Assert (False); --@ASSERT:FAIL
   end P;

   type Int_Acc is access Integer;

   procedure Initialize (My_Int_Acc : out not null Int_Acc) is
   begin
      My_Int_Acc := new Integer'(0);
   end Initialize;

   X : Int_Acc;
begin
   Initialize (X);
end Test_Not_Null_Out;
