with Other;

package Const4
  with Abstract_State => State,
       Initializes    => (State,
                          C,              --  Cannot mention C here
                          V => Other.S)   --  Cannot mention S here
is
   C : constant Integer := 5;
   V : Integer := Other.S;

   function Get_C return Integer
     with Global => C;  --  Cannot mention C here

   procedure P (X : out Integer)
     with Depends => (X => C);  --  Cannot mention C here

   procedure P2
     with Depends => (State => State);
end Const4;
