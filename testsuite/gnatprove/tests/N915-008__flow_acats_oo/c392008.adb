
------------------------------------------------------------------- C392008

with C392008_0;    use C392008_0;          -- package Bank
with C392008_1;    use C392008_1;        -- package Checking;
with C392008_2;    use C392008_2;        -- package Interest_Checking;
with Report;

procedure C392008 is

   package Bank              renames C392008_0;
   package Checking          renames C392008_1;
   package Interest_Checking renames C392008_2;

   B_Acct  : Bank.Account;
   C_Acct  : Checking.Account;
   IC_Acct : Interest_Checking.Account;

   --
   -- Define procedures with class-wide formal parameters of mode IN OUT.
   --

   -- This procedure will perform a dispatching call on the
   -- overridden primitive operation Open.

   procedure New_Account (Acct : in out Bank.Account'Class) is
   begin
      Open (Acct);  -- Dispatch according to tag of class-wide parameter.
   end New_Account;

   -- This procedure will perform a dispatching call on the inherited
   -- primitive operation (for all types derived from the root Bank.Account)
   -- Service_Charge.

   procedure Apply_Service_Charge (Acct: in out Bank.Account'Class) is
   begin
      Service_Charge (Acct);  -- Dispatch according to tag of class-wide parm.
   end Apply_Service_Charge;

   -- This procedure will perform a dispatching call on the
   -- inherited/overridden primitive operation Add_Interest.

   procedure Annual_Interest (Acct: in out Bank.Account'Class) is
   begin
      Add_Interest (Acct);  -- Dispatch according to tag of class-wide parm.
   end Annual_Interest;

begin

   Report.Test ("C392008",  "Check that the use of a class-wide formal "    &
                            "parameter allows for the proper dispatching "  &
                            "of objects to the appropriate implementation " &
                            "of a primitive operation");

   -- Check the dispatch to primitive operations overridden for each
   -- extended type.
   New_Account (B_Acct);
   New_Account (C_Acct);
   New_Account (IC_Acct);

   if (B_Acct.Current_Balance  /= 10_00) or
      (C_Acct.Current_Balance  /= 20_00) or
      (IC_Acct.Current_Balance /= 30_00)
   then
      Report.Failed ("Failed dispatch to multiply overridden prim. oper.");
   end if;


   Annual_Interest (B_Acct);
   Annual_Interest (C_Acct);
   Annual_Interest (IC_Acct); -- Check the dispatch to primitive operation
                              -- overridden from a parent type which inherited
                              -- the operation from the root type.
   if (B_Acct.Current_Balance  /= 10_00) or
      (C_Acct.Current_Balance  /= 20_00) or
      (IC_Acct.Current_Balance /= 90_00)
   then
      Report.Failed ("Failed dispatch to overridden primitive operation");
   end if;


   Apply_Service_Charge (Acct => B_Acct);
   Apply_Service_Charge (Acct => C_Acct);
   Apply_Service_Charge (Acct => IC_Acct); -- Check the dispatch to a
                                           -- primitive operation twice
                                           -- inherited from the root
                                           -- tagged type.
   if (B_Acct.Current_Balance  /=  5_00) or
      (C_Acct.Current_Balance  /= 15_00) or
      (IC_Acct.Current_Balance /= 85_00)
   then
      Report.Failed ("Failed dispatch to Apply_Service_Charge");
   end if;

   Report.Result;

end C392008;
