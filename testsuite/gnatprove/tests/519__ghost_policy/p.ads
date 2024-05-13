package P is

   pragma Assertion_Policy (Ghost => Check);
   X : Integer := 1 with Ghost;

   pragma Assertion_Policy (Ghost => Ignore);
   Y : Integer := X with Ghost;

   pragma Assertion_Policy (Assert => Check);
   pragma Assert (X = 1);

end P;
