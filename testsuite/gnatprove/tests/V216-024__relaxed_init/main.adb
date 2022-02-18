procedure Main with SPARK_Mode is
   type R is record
      B : Boolean;
   end record;

   X : R with Relaxed_Initialization;

begin
   pragma Assert (X.B); -- @INIT_BY_PROOF:FAIL
end Main;
