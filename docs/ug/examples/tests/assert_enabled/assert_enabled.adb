pragma Assertion_Policy (Pre => Check, Post => Ignore);

procedure Assert_Enabled (X : in out Integer) with
  SPARK_Mode,
  Pre  => X > 0,  --  executed at run time
  Post => X > 2   --  ignored at run time
is
   pragma Assertion_Policy (Assert => Check);
   pragma Assert (X >= 0);  --  executed at run time

   pragma Assertion_Policy (Assert => Ignore);
   pragma Assert (X >= 0);  --  ignored at run time
begin
   X := X - 1;
end Assert_Enabled;
