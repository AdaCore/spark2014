package body Volatiles_Legal
  with SPARK_Mode
is
   procedure P1 (Par : in out Vol_Rec_T) is
      Tmp1, Tmp2 : Integer;
   begin
      Par.X := Par.X + 1;  --  No flow error should be issued
      Par.X := Par.X + 1;  --  since all updates are effective.

      Tmp1 := Par.X;
      Tmp2 := Par.X;  --  Since Async_Writers => True for Par,
                      --  Tmp2 might NOT have the same value as Tmp1.

      pragma Assert (Tmp1 = Tmp2);  --  This should NOT be provable.
   end P1;


   procedure P2 is
      Temp : Integer := Vol.X;
   begin
      if Temp <= 0 then
         Vol.X := -1;
      else
         Vol.X := 1;
      end if;

      pragma Assert (if Temp > 0 then Vol.X = 1);  --  This should be provable.
   end P2;


   procedure P3 is
   begin
      Vol2.X := 5;  --  This statement is ineffective since Async_Readers
                    --  and Effective_Writes are set to False.

      Vol2.X := 6;
   end P3;


   procedure P4 (Par : Integer ; Par2 : out Integer)
     with Global  => (In_Out => Vol2),
          Depends => ((Par2,
                       Vol2) => (Vol2,
                                 Par))
   is
   begin
      Vol2.X := Par;
      --  At this point, an external writer might update Vol2.
      --  This is why Vol2 is an In_Out and why Vol2 depends on itself.
      Par2 := Vol2.X;
   end P4;
begin
   P2;  --  This should NOT generate any errors (Vol needs not be initialized).
end Volatiles_Legal;
