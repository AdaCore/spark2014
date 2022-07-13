package body Glob with SPARK_Mode is

   procedure Proc is
   begin
      Y := null;  -- @RESOURCE_LEAK:PASS
      Z := null;  -- @RESOURCE_LEAK:FAIL
   end Proc;

   procedure Wrap_Proc (B : Boolean) is
   begin
      if B then return; end if;
      Proc;  -- @RESOURCE_LEAK:FAIL
   end Wrap_Proc;

   procedure Wrap_Groc is
   begin
      Groc;  -- @RESOURCE_LEAK:FAIL
   end Wrap_Groc;

   procedure Groc is
   begin
      Y := null;  -- @RESOURCE_LEAK:PASS
      if X.all > 0 then
         Z := null;  -- @RESOURCE_LEAK:FAIL
      end if;
   end Groc;

   procedure Local is
      package Loc with
        Initial_Condition => X = null and Y = null and Z = null
      is
         X : T;  -- @RESOURCE_LEAK:PASS
         Y : T;  -- @RESOURCE_LEAK:PASS
         Z : T;  -- @RESOURCE_LEAK:FAIL
      end;
   begin
      Loc.X := new Integer'(0);  -- @RESOURCE_LEAK:PASS
      Loc.Y := null;  -- @RESOURCE_LEAK:PASS
      Loc.Z := Loc.X;  -- @RESOURCE_LEAK:PASS
   end Local;

end Glob;
