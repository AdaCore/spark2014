-- M603-021 - Proof support for Volatile and External Variables
--
-- This package illustrates legality rules for inputs

package Port2
is
   -------------------------------------
   -- Evaluation order and LRM 7.1.3(10)
   -------------------------------------

   V1 : Integer
     with Volatile,
          Async_Writers => True;

   -- Tests a legality rule, so appears in a distinct
   -- package, so that rejection of this unit does not
   -- prevent proof of other units.

   procedure Test_Eval_Order_OK (X : out Boolean)
     with Global => (Input => V1),
          Depends => (X => V1);

end Port2;
