package body Bad_Account with
  SPARK_Mode,
  Refined_State => (State => Total, Prev_State => Last_Incr)
is
   Total : Integer;

   Last_Incr : Integer := Integer'First with Ghost;

   procedure Add_To_Total (Incr : in Integer) with
     Refined_Global => (In_Out => Total,
                        Output => Last_Incr)
   is
   begin
      Total := Total + Incr;
      Last_Incr := Incr;
   end Add_To_Total;

end Bad_Account;
