with Q2; use Q2;
package Q1 with SPARK_Mode is

   --  Check handling of type invariants in nested packages. Tests are
   --  performed in the scope of P1. In this scope, the invariants of T2, T3,
   --  and T5 always hold. Invariants of T1 and T4 might be broken.

   package P1 is
      type T1 is private;
      procedure Q;  -- @INVARIANT_CHECK:FAIL

      package P5 is
         type T5 is private;
      private
         type T5 is new Integer with Type_Invariant => T5 >= 0, Default_Value => 0;
      end P5;

   private
      type T1 is new Integer with Type_Invariant => T1 >= 0, Default_Value => 0;
   end P1;
   use P1;
   use P5;

   package P2 is
      type T2 is private;
   private
      type T2 is new Integer with Type_Invariant => T2 >= 0, Default_Value => 0;
   end P2;
   use P2;

   type T4 is private;

   type R is private;

   procedure P_Vis (X : in out R) with
     Global => null,
     Always_Terminates,
     Import;

private
   type T4 is new Integer with Type_Invariant => T4 >= 0, Default_Value => 0;

   type R is record
      F1 : T1;
      F2 : T2;
      F3 : T3;
      F4 : T4;
      F5 : T5;
   end record;
end Q1;
