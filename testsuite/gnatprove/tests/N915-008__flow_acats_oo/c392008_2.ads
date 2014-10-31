
----------------------------------------------------------------- C392008_2

with C392008_0;             -- with Bank;
with C392008_1;          -- with Checking;

package C392008_2 is     -- package Interest_Checking

   package Bank     renames C392008_0;
   package Checking renames C392008_1;

   subtype Interest_Rate is Bank.Dollar_Amount range 0..100; -- was digits 4;

   Current_Rate : Interest_Rate := 0_02;

   type Account is new Checking.Account with
      record
         Rate : Interest_Rate;
      end record;

   -- Overridden primitive operations.

   procedure Add_Interest (A : in out Account);
   procedure Open         (A : in out Account);

   -- "Twice" inherited primitive operations (from Bank.Account)
   -- procedure Deposit        (A : in out Account;
   --                           X : in     Bank.Dollar_Amount);
   -- procedure Withdrawal     (A : in out Account;
   --                           X : in     Bank.Dollar_Amount);
   -- function  Balance        (A : in     Account) return Bank.Dollar_Amount;
   -- procedure Service_Charge (A : in out Account);

end C392008_2;
