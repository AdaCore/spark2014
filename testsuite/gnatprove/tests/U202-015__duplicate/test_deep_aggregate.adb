procedure Test_Deep_Aggregate with SPARK_Mode is
   type Int_Acc is access Integer;
   type Int_Acc_Array is array (Positive range <>) of Int_Acc;

   A : Int_Acc_Array (1 .. 10) := (others => null);
begin
   null;
end Test_Deep_Aggregate;
