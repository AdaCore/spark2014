procedure Borrower (X : not null access Integer) with SPARK_Mode is
   B : not null access Integer := X with Relaxed_Initialization; -- @INIT_BY_PROOF:FAIL
   --  The contract on Set is not precise enough to ensure that X.all is
   --  initialized at the end of the borrow. A more precise contract cannot be
   --  written for now, as the parameter and return types of At_End_Borrow
   --  functions on access types cannot have the Relaxed_Initialization
   --  annotation, being non-composite types. Introducing an attribute for
   --  At_End_Borrow would solve the issue.

   procedure Set with Global => (In_Out => B),
     Post => B'Initialized and B.all = 9
    is
   begin
      B.all := 9;
   end Set;
begin
   Set;
end Borrower;
