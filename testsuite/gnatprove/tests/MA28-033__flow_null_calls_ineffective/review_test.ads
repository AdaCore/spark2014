with Logging;

package Review_Test
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => (State, Var)
is
   Var : Integer := 0;

   procedure Does_Something (A : out Integer)
     with Global  => (State, Var, Logging.Testpoint),
          Depends => (A    => State,
                      null => (Var, Logging.Testpoint));
end Review_Test;
