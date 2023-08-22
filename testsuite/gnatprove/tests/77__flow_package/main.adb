procedure Main (C : Boolean; X : in out Boolean) is

   --  The following packages have identical specs

   package P with Initializes => null is
      procedure Dummy with Global => null;
   end;

   package Q with Initializes => null is
      procedure Dummy with Global => null;
   end;

   --  The following bodies have IF-condition negated and THEN/ELSE branches
   --  flipped, so semantically they are identical.

   package body P is
      procedure Dummy is null;
   begin
      if C then
         pragma Assert (X);
      else
         X := not X;
      end if;
   end;

   package body Q is
      procedure Dummy is null;
   begin
      if not C then
         X := not X;
      else
         pragma Assert (X);
      end if;
   end;

   --  We prefer flow analysis to emit the same checks for code that is
   --  semantically identical.

begin
   X := not X;  --  dummy use of X
end;
