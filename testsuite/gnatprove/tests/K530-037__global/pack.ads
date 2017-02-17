package Pack is

   type Account_Types  is (Bank, Savings, Preferred, Total);
   type Account_Counter is array (Account_Types) of Integer;

   Number_Of_Accounts : Account_Counter := (Bank      => 0,
                                            Savings   => 0,
                                            Preferred => 0,
                                            Total     => 0);
end Pack;
