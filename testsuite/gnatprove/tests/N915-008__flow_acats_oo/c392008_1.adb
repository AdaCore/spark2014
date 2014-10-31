
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

package body C392008_1 is

   -- Overridden primitive operation.

   procedure Open (A : in out Account) is
      Check_Guarantee : Bank.Dollar_Amount := 10_00;
      Initial_Deposit : Bank.Dollar_Amount := 20_00;
   begin
      A.Current_Balance := Initial_Deposit;
      A.Overdraft_Fee   := Check_Guarantee;
   end Open;

end C392008_1;
