with Identity;
use type Identity.Id;

package body Database is
   pragma Unevaluated_Use_Of_Old (Allow);
   --------------------
   -- Local Packages --
   --------------------

   --  Availability of accounts is managed in a separate package, which offers
   --  two procedures to reserve a previously unused account or to make one
   --  available when not used anymore, and a function to query if there is at
   --  least one account available.

   package Availability is

      type Account_Link is record
         Available  : Boolean;
         Prev, Next : Ext_Account_Num;
      end record;

      No_Account_Link : constant Account_Link :=
                          Account_Link'(Available => False,
                                        Prev      => No_Account_Num,
                                        Next      => No_Account_Num);

      type Account_Link_Data is array (Database.Account_Num) of Account_Link;

      Links : Account_Link_Data :=
                Account_Link_Data'(others => No_Account_Link);

      First_Available : Ext_Account_Num := Account_Num'First;

      function Some_Available return Boolean is
        (First_Available /= No_Account_Num);

      function Is_Available (Account : in Account_Num) return Boolean is
        (Links (Account).Available);

      procedure Reserve_First_Available (Account : out Account_Num)
      with
        Pre  => Some_Available,
        Post => not Is_Available (Account) and then
                (for all Act in Account_Num =>
                   (if Act /= Account then
                      Links (Act).Available = Links'Old (Act).Available));

      procedure Make_Available (Account : Account_Num)
      with
        Pre  => not Is_Available (Account),
        Post => Is_Available (Account) and then
                (for all Act in Account_Num =>
                   (if Act /= Account then
                      Links (Act).Available = Links'Old (Act).Available));

      function Num_Available return Natural;

   end Availability;

   -------------------------------
   -- Local Types and Constants --
   -------------------------------

   --  An account relates an account number to an owner, whose name and id are
   --  recorded.

   type Account_Rec is record
      Owner_Name : Identity.Name;
      Owner_Id   : Identity.Id;
      Account    : Ext_Account_Num;
   end record;

   No_Account_Rec : constant Account_Rec :=
                      Account_Rec'(Owner_Name => Identity.No_Name,
                                   Owner_Id   => Identity.No_Id,
                                   Account    => No_Account_Num);

   --  The account balance relates an account number to an amount of money

   type Account_Balance is record
      Value   : Money.Amount;
      Account : Ext_Account_Num;
   end record;

   No_Account_Balance : constant Account_Balance :=
                          Account_Balance'(Value   => Money.No_Amount,
                                           Account => No_Account_Num);

   type Account_Data is array (Account_Num) of Account_Rec;
   type Account_Balance_Data is array (Account_Num) of Account_Balance;

   ---------------------
   -- Local Variables --
   ---------------------

   Accounts         : Account_Data := Account_Data'(others => No_Account_Rec);
   --  Database of account identity data

   Accounts_Balance : Account_Balance_Data :=
                        Account_Balance_Data'(others => No_Account_Balance);
   --  Database of account balance data

   ------------------
   -- Availability --
   ------------------

   package body Availability is

      procedure Reserve_First_Available (Account : out Account_Num) is
      begin
         Account := First_Available;
         Links (First_Available).Available := False;
         First_Available := Links (First_Available).Next;
      end Reserve_First_Available;

      procedure Make_Available (Account : Account_Num) is
      begin
         --  Remove node Account from linked-list

         if Links (Account).Prev /= No_Account_Num then
            Links (Links (Account).Prev).Next := Links (Account).Next;
         end if;
         if Links (Account).Next /= No_Account_Num then
            Links (Links (Account).Next).Prev := Links (Account).Prev;
         end if;

         --  Insert node Account into linked-list as first available node

         if First_Available /= No_Account_Num then
            Links (Account).Prev := Links (First_Available).Prev;
         end if;
         Links (Account).Next := First_Available;
         Links (Account).Available := True;
         First_Available := Account;
      end Make_Available;

      function Num_Available return Natural is
         Count : Natural := 0;
      begin
         for I in Account_Num loop
            pragma Assert (Count < Natural(I));
            if Is_Available (I) then
               Count := Count + 1;
            end if;
         end loop;
         return Count;
      end Num_Available;

      procedure Initialize_Links is
         Tmp_Prev : Ext_Account_Num;
         Tmp_Next : Ext_Account_Num;
      begin
         for I in Account_Num loop
            if I = Account_Num'First then
               Tmp_Prev := No_Account_Num;
            else
               Tmp_Prev := I - 1;
            end if;
            if I = Account_Num'Last then
               Tmp_Next := No_Account_Num;
            else
               Tmp_Next := I + 1;
            end if;
            Links (I) := Account_Link'(Available => True,
                                       Prev      => Tmp_Prev,
                                       Next      => Tmp_Next);
         end loop;
      end Initialize_Links;

   begin
      Initialize_Links;
   end Availability;

   -------------------------
   -- Max_Account_Reached --
   -------------------------

   function Max_Account_Reached return Boolean is
     (not Availability.Some_Available);

   ------------------
   -- Num_Accounts --
   ------------------

   function Num_Accounts return Natural is
   begin
      return Availability.Num_Available;
   end Num_Accounts;

   --------------
   -- Existing --
   --------------

   function Existing (Account : in Account_Num) return Boolean is
      (not Availability.Is_Available (Account));

   ----------------
   -- Belongs_To --
   ----------------

   function Belongs_To
     (Account  : in Account_Num;
      Customer : in Identity.Name;
      Id       : in Identity.Id) return Boolean
   is
     (Accounts (Account) = Account_Rec'(Owner_Name => Customer,
                                        Owner_Id   => Id,
                                        Account    => Account));
   -------------
   -- Balance --
   -------------

   function Balance (Account : Account_Num) return Money.Amount is
      (Accounts_Balance (Account).Value);

   --------------
   -- Currency --
   --------------

   function Currency (Account : in Account_Num) return Money.CUR is
      (Accounts_Balance (Account).Value.Currency);

   ----------
   -- Open --
   ----------

   procedure Open
     (Customer : in     Identity.Name;
      Id       : in     Identity.Id;
      Cur      : in     Money.CUR;
      Account  :    out Account_Num) is
   begin
      --  Defensive programming if precondition is not checked at run-time

      if Max_Account_Reached then
         Account := Max_Account_Num;
         return;
      end if;

      Availability.Reserve_First_Available (Account);
      Accounts (Account) := Account_Rec'(Owner_Name => Customer,
                                         Owner_Id   => Id,
                                         Account    => Account);
      Accounts_Balance (Account) :=
        Account_Balance'(Value   => Money.Amount'(Currency => Cur,
                                                  Raw      => 0),
                         Account => Account);
   end Open;

   -----------
   -- Close --
   -----------

   procedure Close
     (Customer : Identity.Name;
      Id       : Identity.Id;
      Account  : Account_Num) is
   begin
      --  Defensive programming if precondition is not checked at run-time

      if Balance (Account).Raw /= 0 then
         return;
      end if;

      --  Perform basic checks on name and identity of account owner. Only
      --  delete the account if the checks are successful.

      if Accounts (Account).Owner_Name = Customer
        and then Accounts (Account).Owner_Id = Id
      then
         Accounts (Account) := No_Account_Rec;
         Availability.Make_Available (Account);
      end if;
   end Close;

   -------------
   -- Deposit --
   -------------

   procedure Deposit (Account : Account_Num; Sum : Money.Amount) is
   begin
      --  Defensive programming if precondition is not checked at run-time

      if Currency (Account) /= Sum.Currency
        or else Balance (Account).Raw + Sum.Raw > Money.Raw_Amount'Last
      then
         return;
      end if;

      Accounts_Balance (Account).Value :=
        Accounts_Balance (Account).Value + Sum;
   end Deposit;

   --------------
   -- Withdraw --
   --------------

   procedure Withdraw (Account : in Account_Num; Sum : in Money.Amount) is
   begin
      --  Defensive programming if precondition is not checked at run-time

      if Currency (Account) /= Sum.Currency
        or else Sum.Raw > Balance (Account).Raw
      then
         return;
      end if;

      Accounts_Balance (Account).Value :=
        Accounts_Balance (Account).Value - Sum;
   end Withdraw;

end Database;
