procedure Q with SPARK_Mode is
   type R (B : Boolean := True) is record
      F : Integer;
   end record;

   type Holder is record
      C : R;
   end record;

   procedure Uninit (X : out R) with
     Depends => (X => null),
     Exceptional_Cases => (Program_Error => True);

   procedure Uninit (X : out R) is
   begin
      raise Program_Error;
   end Uninit;

   procedure Uninit_2 (X : out R) with
     Depends => (X => null),
     Relaxed_Initialization => X,
     Exceptional_Cases => (Program_Error => True),
     Post => X'Initialized;

   procedure Uninit_2 (X : out R) is
   begin
      raise Program_Error;
   end Uninit_2;

   X : R := (True, 12);
   Y : Holder := (C => (True, 12)) with Relaxed_Initialization;
begin
   Uninit_2 (X);
   Uninit (Y.C);
exception
   when Program_Error =>
      pragma Assert (X.B);    -- @INITIALIZED:CHECK Initialization check by flow: the discriminant of X might have been uninitialized by the call
      pragma Assert (Y.C.B);  -- @INIT_BY_PROOF:FAIL Initialization check by proof: the discriminant of X might have been uninitialized by the call
end;
