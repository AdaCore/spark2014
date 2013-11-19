package Raw_Data
  with SPARK_Mode,
       Abstract_State => (State with External => Async_Writers),
       Initializes    => State
is
   function Data_Is_Valid return Boolean
     with Global => State;

   function Get_Value return Integer
     with Global => State;

   procedure Read_Next
     with Global  => (In_Out => State),
          Depends => (State => State);
end Raw_Data;
