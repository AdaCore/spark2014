package Dispatch_Check with SPARK_Mode is
   type I is new Integer with Relaxed_Initialization;
   type Root is abstract tagged record
      F : I;
   end record;

   --  The abstract primitive is checked through its dispatching contract
   procedure P (X, Y, Z : Root) is abstract with
     Global => null,
     Pre'Class => X.F'Initialized and then Y.F'Initialized
       and then X in Y
         | Z; -- @INIT_BY_PROOF:FAIL
end Dispatch_Check;
