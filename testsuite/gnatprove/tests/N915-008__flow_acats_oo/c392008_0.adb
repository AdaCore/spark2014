
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

package body C392008_0 is

   -- Primitive operations for type Account.

   procedure Deposit (A : in out Account;
                      X : in     Dollar_Amount) is
   begin
      A.Current_Balance := A.Current_Balance + X;
   end Deposit;

   procedure Withdrawal(A : in out Account;
                        X : in     Dollar_Amount) is
   begin
      A.Current_Balance := A.Current_Balance - X;
   end Withdrawal;

   function  Balance (A : in     Account) return Dollar_Amount is
   begin
      return (A.Current_Balance);
   end Balance;

   procedure Service_Charge (A : in out Account) is
   begin
      A.Current_Balance := A.Current_Balance - 5_00;
   end Service_Charge;

   procedure Add_Interest (A : in out Account) is
      Interest_On_Account : Dollar_Amount := 0_00;
   begin
      A.Current_Balance := A.Current_Balance + Interest_On_Account;
   end Add_Interest;

   procedure Open (A : in out Account) is
      Initial_Deposit : Dollar_Amount := 10_00;
   begin
      A.Current_Balance := Initial_Deposit;
   end Open;

end C392008_0;
