pragma SPARK_Mode(On);
with P; pragma Elaborate_All (P);
package Try_Init_4
   with Abstract_State => (X, Y),
        Initializes => (X,
                        Y => P.S,
                        null => P.V)
is
   -- Attempting to initialize this constant with a variable
   -- is currently (but erroneously) not allowed by the RM.
   -- This is the proposed way of denoting state abstractions and variables
   -- which are read during package elaboration not used in the initialization
   -- of any state abstractions or variables of the package.
   -- This Initialization aspect is currently rejected by the front end.
   C : constant Integer := P.V;
end Try_Init_4;
