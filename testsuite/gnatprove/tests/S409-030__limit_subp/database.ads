with Identity;
with Money; use Money;

package Database is

   --  Accounts are numbered from 0 (invalid account) to Max_Account_Num.
   --  Valid accounts start at 1. Not all account numbers correspond to valid
   --  accounts.

   Max_Account_Num : constant := 200_000;
   type Ext_Account_Num is range 0 .. Max_Account_Num;
   subtype Account_Num is Ext_Account_Num range 1 .. Max_Account_Num;

   No_Account_Num : constant Ext_Account_Num := 0;

   --  Logical queries used in contracts

   function Existing (Account : in Account_Num) return Boolean;

   function Belongs_To
     (Account  : in Account_Num;
      Customer : in Identity.Name;
      Id       : in Identity.Id) return Boolean;

   function Num_Accounts return Natural;

   function Max_Account_Reached return Boolean;

   function Currency (Account : in Account_Num) return Money.CUR;

   --  Basic account management facilities

   function Balance (Account : in Account_Num) return Money.Amount
   with
     Pre => Existing (Account),
     Test_Case => (Name     => "existing account",
                   Mode     => Nominal,
                   Ensures  => Balance'Result.Currency = Currency (Account)),
     Test_Case => (Name     => "unknown account",
                   Mode     => Robustness,
                   Requires => not Existing (Account),
                   Ensures  => Balance'Result = No_Amount);

   procedure Open
     (Customer : in     Identity.Name;
      Id       : in     Identity.Id;
      Cur      : in     Money.CUR;
      Account  :    out Account_Num)
   with
     Pre  => not Max_Account_Reached,
     Post => Existing (Account)
               and then Belongs_To (Account, Customer, Id)
               and then Money.Is_Empty (Balance (Account)),
     Test_Case => (Name     => "first account",
                   Mode     => Nominal,
                   Requires => Num_Accounts = 0,
                   Ensures  => Num_Accounts = 1),
     Test_Case => (Name     => "common case",
                   Mode     => Nominal,
                   Requires => Num_Accounts > 0,
                   Ensures  => Num_Accounts = Num_Accounts'Old + 1),
     Test_Case => (Name     => "max account reached",
                   Mode     => Robustness,
                   Requires => Max_Account_Reached,
                   Ensures  => Account = Max_Account_Num);

   procedure Close
     (Customer : in Identity.Name;
      Id       : in Identity.Id;
      Account  : in Account_Num)
   with
     Pre  => Existing (Account)
               and then Belongs_To (Account, Customer, Id)
               and then Money.Is_Empty (Balance (Account)),
     Test_Case => (Name     => "last account",
                   Mode     => Nominal,
                   Requires => Num_Accounts = 1,
                   Ensures  => Num_Accounts = 0),
     Test_Case => (Name     => "common case",
                   Mode     => Nominal,
                   Requires => Num_Accounts > 1,
                   Ensures  => Num_Accounts = Num_Accounts'Old - 1),
     Test_Case => (Name     => "non-null balance",
                   Mode     => Robustness,
                   Requires => not Money.Is_Empty (Balance (Account)),
                   Ensures  => Existing (Account) and
                               Balance (Account) = Balance (Account)'Old);

   procedure Deposit (Account : in Account_Num; Sum : in Money.Amount)
   with
     Pre  => Existing (Account) and then
             Currency (Account) = Sum.Currency and then
             Balance (Account).Raw + Sum.Raw <= Money.Raw_Amount'Last,
     Post => Balance (Account) = Balance (Account)'Old + Sum,
     Test_Case => (Name     => "common case",
                   Mode     => Nominal),
     Test_Case => (Name     => "different currency",
                   Mode     => Robustness,
                   Requires => Currency (Account) /= Sum.Currency,
                   Ensures  => Balance (Account) = Balance (Account)'Old),
     Test_Case => (Name     => "too large",
                   Mode     => Robustness,
                   Requires => Balance (Account).Raw + Sum.Raw >
                                 Money.Raw_Amount'Last,
                   Ensures  => Balance (Account) = Balance (Account)'Old);

   procedure Withdraw (Account : in Account_Num; Sum : in Money.Amount)
   with
     Pre  => Existing (Account) and then
             Currency (Account) = Sum.Currency and then
             Sum.Raw <= Balance (Account).Raw,
     Post => Balance (Account) = Balance (Account)'Old - Sum,
     Test_Case => (Name     => "common case",
                   Mode     => Nominal),
     Test_Case => (Name     => "different currency",
                   Mode     => Robustness,
                   Requires => Currency (Account) /= Sum.Currency,
                   Ensures  => Balance (Account) = Balance (Account)'Old),
     Test_Case => (Name     => "too large",
                   Mode     => Robustness,
                   Requires => Sum.Raw > Balance (Account).Raw,
                   Ensures  => Balance (Account) = Balance (Account)'Old);

end Database;
