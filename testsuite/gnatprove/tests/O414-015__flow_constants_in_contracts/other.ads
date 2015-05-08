package Other
  with Initializes => (V, C)
is
   V :          Integer := 0;

   C : constant Integer := V;  --  Constant with variable input

   S : constant Integer := 0;  --  Constant without variable input

   function Gimme_C return Integer
     with Pre => True;

   function Gimme_V_Plus_C return Integer
     with Pre => True;

   function Gimme_Zero return Integer
     with Pre => True;

   function Identity (X : Integer) return Integer
     with Global => null,
          Post   => Identity'Result = X;
end Other;
