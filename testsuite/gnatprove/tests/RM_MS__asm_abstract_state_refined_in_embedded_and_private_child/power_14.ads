-- Use of child package and embedded package to encapsulate state
package Power_14
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => State
is
   procedure Read_Power(Level : out Integer)
     with Global  => State,
          Depends => (Level => State);
end Power_14;
