package body Volatiles_Legal
  with SPARK_Mode
is

   --  Requires volatile parameters (not implemented yet).

   procedure P1 (Par : in out Vol_Rec_T) is
      Tmp1, Tmp2 : Integer;
   begin
      Par.X := Par.X;  --  No flow error should be issued
      Par.X := Par.X;  --  since all updates are effective.

      Tmp1 := Par.X;
      Tmp2 := Par.X;  --  Since Async_Writers => True for Par,
                      --  Tmp2 might NOT have the same value as Tmp1.

      pragma Assert (Tmp1 = Tmp2);  --  @ASSERT:FAIL
   end P1;

   procedure P2 is
      Temp : Integer := Vol.X;
   begin
      if Temp <= 0 then
         Vol.X := -1;
      else
         Vol.X := 1;
      end if;

      pragma Assert (if Temp > 0 then Vol.X = 1);  --  @ASSERT:PASS
   end P2;

   procedure P3 is
   begin
      Vol2.X := 5;  --  warning: unused assignment

      Vol2.X := 6;
   end P3;
begin
   Vol := (X => 5);
   --  This should NOT generate any errors (Vol2 needs not be initialized).
end Volatiles_Legal;
