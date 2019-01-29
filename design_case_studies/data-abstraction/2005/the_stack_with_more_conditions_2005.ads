package The_Stack_With_More_Conditions
--# own State;
--# initializes State;
--  The "Initial_Condition => Is_Empty" statement cannot be replicated in SPARK 2005.
is
   function Is_Empty return Boolean;
   --# global State;

   function Is_Full return Boolean;
   --# global State;

   function Top return Integer;
   --# global State;
   --# pre not Is_Empty (State);

   procedure Push(X: in Integer);
   --# global in out State;
   --# pre  not Is_Full (State);
   --# post Top (State) = X;

   procedure Pop(X: out Integer);
   --# global in out State;
   --# pre not Is_Empty (State);

   procedure Swap(X: in Integer);
   --# global in out State;
   -- We cannot have conditional global contracts in SPARK 2005.
   --# pre  not Is_Empty (State);
   --# post Top (State) = X;

end The_Stack_With_More_Conditions;
