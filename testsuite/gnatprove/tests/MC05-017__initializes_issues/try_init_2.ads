pragma SPARK_Mode(On);
with P;
package Try_Init_2
   with Initializes => (null => P.V)
is
   -- Attempting to initialize this constant with a variable
   -- is currently (but erroneously) not allowed by the RM.
   -- It gives a misleading error message because C cannot be
   -- an initialized item in an Initializes aspect.
   -- The suggested revisions of the RM for Initializes aspects
   -- allows a null as an initializee (nee inititialization item).
   -- The syntax of the current RM does not allow this but the compiler FE
   -- does accept the above Initializes aspect.
   -- However the above Initializes aspect crashes the flow analyser.
   C : constant Integer := P.V;
end Try_Init_2;
