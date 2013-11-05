pragma SPARK_Mode (On);
package Input_Port_14
  with Abstract_State => (Input_State with External => Async_Writers)
is
   procedure Read_From_Port(Input_Value : out Integer)
     with Global  => (Input => Input_State),
          Depends => (Input_Value => Input_State);
end Input_Port_14;
