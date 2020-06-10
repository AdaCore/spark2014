-- M603-021 - Proof support for Volatile and External Variables
--
-- This package illustrates legality rules for inputs

with System.Storage_Elements;

package Port2
is
   -------------------------------------
   -- Evaluation order and LRM 7.1.3(10)
   -------------------------------------

   V1 : Integer
     with Volatile,
          Async_Writers => True;

   C : constant Integer
   with Volatile,
        Import,
        Convention => C,
        Address => System.Storage_Elements.To_Address (16#F00BA5#);

   -- Tests a legality rule, so appears in a distinct
   -- package, so that rejection of this unit does not
   -- prevent proof of other units.

   procedure Test_Eval_Order_Bad1 (X : out Boolean)
     with Global => (Input => V1),
          Depends => (X => V1);

   procedure Test_Eval_Order_Bad2 (X : out Boolean)
     with Global => (Input => V1),
          Depends => (X => V1);

end Port2;
