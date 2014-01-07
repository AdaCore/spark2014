pragma SPARK_Mode(On);
with P;
package Try_Init_1
   with Initializes => (C => P.V)
is
   -- Attempting to initialize this constant with a variable
   -- is currently (but erroneously) not allowed by the RM.
   -- It gives a misleading error message because C cannot be
   -- an initialized item in an Initializes aspect.
   -- If we try and add an Initializes aspect with C as an
   -- initialization item we correctly get the message that
   -- "initialization item must denote variable or state"
   C : constant Integer := P.V;
end Try_Init_1;
