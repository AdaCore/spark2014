-- Use of child packages to encapsulate state
pragma SPARK_Mode (On);
package Power_14
   with Abstract_State => State,
        Initializes    => State
is
   procedure Read_Power(Level : out Integer)
     with Global  => State,
          Depends => (Level => State);
end Power_14;
