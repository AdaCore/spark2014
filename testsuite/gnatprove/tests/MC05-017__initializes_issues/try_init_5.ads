pragma SPARK_Mode(On);
with P;
package Try_Init_5
   with Initializes => (Not_Used => P.V)
is
   -- Attempting to initialize this constant with a variable
   -- is currently (but erroneously) not allowed by the RM.
   -- The work around is to introduce a variable - in this case it
   -- has to be visible but where the constant is deferred or declared
   -- in the body the variable could be represented as a state abstraction.
   Not_Used : Integer := P.V;
   C : constant Integer := P.V;
end Try_Init_5;
