package Money is

   --  An amount of mone is always qualified by the currency in which it is
   --  expressed. None corresponds to the invalid currency.

   type CUR is (None, Dollar, Euro, Linden, RMB, Yen, Your_Favorite_Currency);

   --  Raw amounts of money range from 0 to 1 million units. The base type for
   --  raw amounts safely allows adding or subtracting two amounts without any
   --  possible overflow.

   type Raw_Amount_Base is range -1_000_000 .. 2_000_000;
   type Raw_Amount is new Raw_Amount_Base range 0 .. 1_000_000;

   type Amount is record
      Currency : CUR;
      Value    : Raw_Amount;
   end record;

   No_Amount : constant Amount := Amount'(Currency => None,
                                          Value    => 0);

   --  Basic arithmetic operations over amounts of money. All arguments should
   --  be in the same currency, and the result is returned in this currency.

   function "+" (A, B : Amount) return Amount
   with
     Pre  => A.Currency = B.Currency and A.Value + B.Value <= Raw_Amount'Last,
     Post => "+"'Result = Amount'(A.Currency, A.Value + B.Value);

   function "-" (A, B : Amount) return Amount
   with
     Pre  => A.Currency = B.Currency and B.Value <= A.Value,
     Post => "-"'Result = Amount'(A.Currency, A.Value - B.Value);

end Money;
