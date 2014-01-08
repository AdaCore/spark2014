pragma SPARK_Mode(On);
with P;
package Try_Init_5
   with Initializes => (Not_Used => P.V)
is
   -- Attempting to initialize this constant with a variable
   -- is currently (but erroneously) not allowed by the RM.
   -- The work around is to introduce a visible variable as here or
   -- a state abstraction for a variable declared in the body. In either case
   -- the variable should be initialized using the variable or state abstraction
   -- from the other package.
   Not_Used : Integer := P.V;
   C : constant Integer := P.V;
end Try_Init_5;
