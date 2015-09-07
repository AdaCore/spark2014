pragma SPARK_Mode(On);
package TickTock
  with
    Abstract_State => TickTock_State,
    Initializes    => TickTock_State
is
   procedure Tick
     with
       Global => (In_Out => TickTock_State),
       Depends => (TickTock_State =>+ null);
end TickTock;
