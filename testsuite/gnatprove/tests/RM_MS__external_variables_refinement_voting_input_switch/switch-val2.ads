private package Switch.Val2
  with SPARK_Mode,
       Abstract_State => (State with External => Async_Writers,
                                     Part_Of  => Switch.State)
is
   function Read return Switch.Reading
     with Global => (Input => State);
end Switch.Val2;
