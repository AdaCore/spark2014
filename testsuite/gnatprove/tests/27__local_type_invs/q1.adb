package body Q1 with SPARK_Mode is

   procedure P_Priv (X : in out R) with
     Global => null,
     Always_Terminates,
     Import;

   package body P1 is

      --  The invariant of T1 and T4 might be broken here. Both need to hold to
      --  call P_Vis. The invariant of T1 only is necessary to call P_Priv.

      procedure Q1 (X : in out R) is
      begin
         P_Vis (X);  -- @INVARIANT_CHECK:FAIL
      end Q1;

      procedure Q2 (X : in out R) with Pre => X.F1 >= 0;
      procedure Q2 (X : in out R) is
      begin
         P_Vis (X);  -- @INVARIANT_CHECK:FAIL
      end Q2;

      procedure Q3 (X : in out R) with Pre => X.F4 >= 0;
      procedure Q3 (X : in out R) is
      begin
         P_Vis (X);  -- @INVARIANT_CHECK:FAIL
      end Q3;

      procedure Q4 (X : in out R) with Pre => X.F1 >= 0 and X.F4 >= 0;
      procedure Q4 (X : in out R) is
      begin
         P_Vis (X);  -- @INVARIANT_CHECK:PASS
      end Q4;

      procedure Q5 (X : in out R) is
      begin
         P_Priv (X);  -- @INVARIANT_CHECK:FAIL
      end Q5;

      procedure Q6 (X : in out R) with Pre => X.F1 >= 0;
      procedure Q6 (X : in out R) is
      begin
         P_Priv (X);  -- @INVARIANT_CHECK:PASS
      end Q6;

      procedure Q7 (X : in out R) with Pre => X.F1 >= 0;
      procedure Q7 (X : in out R) is
        procedure P_Loc (X : in out R) with
          Global => null,
          Always_Terminates,
          Import;
      begin
         P_Loc (X);  -- @INVARIANT_CHECK:NONE
      end Q7;

      --  All invariants should hold for globals before and after the subprogram.
      --  P_Priv might leave G in a state where T4 is broken.

      G : R;
      procedure Q is
      begin
         P_Vis (G);  -- @INVARIANT_CHECK:PASS
         P_Priv (G);
      end Q;
   end P1;
end Q1;
