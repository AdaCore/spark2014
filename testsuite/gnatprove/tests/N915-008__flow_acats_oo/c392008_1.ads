
----------------------------------------------------------------- C392008_1

with C392008_0;              -- package Bank

package C392008_1 is      -- package Checking

   package Bank renames C392008_0;

   type Account is new Bank.Account with
      record
         Overdraft_Fee : Bank.Dollar_Amount;
      end record;

   -- Overridden primitive operation.

   procedure Open (A : in out Account);

   -- Inherited primitive operations.
   -- procedure Deposit        (A : in out Account;
   --                           X : in     Bank.Dollar_Amount);
   -- procedure Withdrawal     (A : in out Account;
   --                           X : in     Bank.Dollar_Amount);
   -- function  Balance        (A : in     Account) return Bank.Dollar_Amount;
   -- procedure Service_Charge (A : in out Account);
   -- procedure Add_Interest   (A : in out Account);

end C392008_1;
