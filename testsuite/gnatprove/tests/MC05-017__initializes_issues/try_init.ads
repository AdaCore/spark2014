pragma SPARK_Mode(On);
with P; pragma Elaborate_All (P);
package Try_Init
is
   -- Attempting to initialize this constant with a variable
   -- is currently (but erroneously) not allowed by the RM.
   -- It gives a misleading error message because C cannot be
   -- an initialized item in an Initializes aspect.
   C : constant Integer := P.V;
end Try_Init;
