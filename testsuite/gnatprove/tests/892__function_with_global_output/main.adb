procedure Main with SPARK_Mode is
   type R is record
      F, G : Integer;
   end record;

   X : R := (1, 2) with Relaxed_Initialization;

   function F return Boolean with
     Side_Effects,
     Pre => X'Initialized,
     Post => X'Initialized and F'Result,
     Global => (Output => X),
     Depends => ((X, F'Result) => null),
     Always_Terminates;

   function F return Boolean is
   begin
      return True;
   end F;

   B : Boolean;
begin
   B := F;  --  @PRECONDITION:FAIL
end Main;
