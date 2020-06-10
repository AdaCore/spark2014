package body Glob with SPARK_Mode is

   procedure Proc is
   begin
      Y := null;  -- @MEMORY_LEAK:PASS
      Z := null;  -- @MEMORY_LEAK:FAIL
   end Proc;

   procedure Wrap_Proc (B : Boolean) is
   begin
      if B then return; end if;
      Proc;  -- @MEMORY_LEAK:FAIL
   end Wrap_Proc;

   procedure Wrap_Groc is
   begin
      Groc;  -- @MEMORY_LEAK:FAIL
   end Wrap_Groc;

   procedure Groc is
   begin
      Y := null;  -- @MEMORY_LEAK:PASS
      if X.all > 0 then
         Z := null;  -- @MEMORY_LEAK:FAIL
      end if;
   end Groc;

   procedure Local is
      package Loc with
        Initial_Condition => X = null and Y = null and Z = null
      is
         X : T;  -- @MEMORY_LEAK:PASS
         Y : T;  -- @MEMORY_LEAK:PASS
         Z : T;  -- @MEMORY_LEAK:FAIL
      end;
   begin
      Loc.X := new Integer'(0);  -- @MEMORY_LEAK:PASS
      Loc.Y := null;  -- @MEMORY_LEAK:PASS
      Loc.Z := Loc.X;  -- @MEMORY_LEAK:PASS
   end Local;

end Glob;
