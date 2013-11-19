with P_14;
pragma Elaborate_All (P_14); -- Required because P_14.Global_Var
                             -- Is mentioned as input in the Initializes aspect
package R_14
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => (State => P_14.Global_Var)
is
   procedure Op ( X : in Positive)
     with Global => (In_Out => State);
end R_14;
