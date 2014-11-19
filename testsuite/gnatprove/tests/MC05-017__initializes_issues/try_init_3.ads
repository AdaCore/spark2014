pragma SPARK_Mode(On);
with P; pragma Elaborate_All (P);
package Try_Init_3
   with Abstract_State => (X, Y),
        Initializes => (Y => P.V)
is
   -- Attempting to initialize this constant with a variable
   -- is currently (but erroneously) not allowed by the RM.
   -- In the current implementation, if the variable is also used in the
   -- initialization of a state abstraction or variable no error is raised
   -- and no flow errors are reported.
   -- This is ok if Y really does depend on P.V.
   -- However, the proposed revision to the RM requires the null initializee
   -- to represent the constant - we could soften this requirement.
   C : constant Integer := P.V;
end Try_Init_3;
