package Other
  with Initializes => (V, C)
is
   V :          Integer := 0;

   C : constant Integer := V;  --  Constant with variable input

   function Gimme_V_Plus_C return Integer
     with Pre => True;

end Other;
