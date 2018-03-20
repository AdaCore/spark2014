package A
with SPARK_Mode
is
    Max_Account : constant := 10;

    type Money is new Natural;
    type Account_Num is new Positive range 1 .. Max_Account;

    type State is private;
private
    type Account is record
       M : Money;
       C : Boolean;
    end record;
    Next_Account : Positive := Natural (Account_Num'First);
    type State is array (Account_Num) of Account
      with Type_Invariant => (for all I in State'Range =>
                               (if Integer (I) >= Next_Account then State (I).C));
    Accounts : State := (others => (M => 0, C => True));
end A;
