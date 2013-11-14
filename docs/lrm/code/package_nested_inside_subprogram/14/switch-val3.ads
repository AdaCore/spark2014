pragma SPARK_Mode (On);
private package Switch.Val3
  with Abstract_State => (State with External => Async_Writers,
                                     Part_Of  => Switch.State)
is
   function Read return Switch.Reading
     with Global => (Input => State);
end Switch.Val3;
