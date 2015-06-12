pragma Assertion_Policy (Pre => Check, Post => Disable);

procedure Assert_Disabled (X : in out Integer) with
  SPARK_Mode,
  Pre  => X > 0,  --  executed at run time
  Post => X > 2   --  ignored at compile time and in analysis
is
   pragma Assertion_Policy (Assert => Check);
   pragma Assert (X >= 0);  --  executed at run time

   pragma Assertion_Policy (Assert => Disable);
   pragma Assert (X >= 0);  --  ignored at compile time and in analysis
begin
   X := X - 1;
end Assert_Disabled;
