procedure P with SPARK_Mode is
   type R (B : Boolean := True) is record
      F : Integer;
   end record;

   procedure Uninit (X : out R) with
     Depends => (X => null),
     Exceptional_Cases => (Program_Error => True);

   procedure Uninit (X : out R) is
   begin
      raise Program_Error;
   end Uninit;

   X : R := (True, 12) with Relaxed_Initialization;
begin
   Uninit (X);  -- @INIT_BY_PROOF:FAIL  For now, we emit a check for the initialization of top-level mutable discriminants with relaxed init even if they are not read.
exception
   when Program_Error =>
      pragma Assert (X.B);  --  Here the discriminant of X should not be read as it might have been uninitialized by the call
end;
