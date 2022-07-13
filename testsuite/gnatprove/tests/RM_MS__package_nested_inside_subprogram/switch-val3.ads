private package Switch.Val3
  with SPARK_Mode,
       Abstract_State => (State with External => Async_Writers,
                                     Part_Of  => Switch.State)
is
   function Read return Switch.Reading
     with Volatile_Function,
          Global   => (Input => State),
          Annotate => (GNATprove, Always_Return);
end Switch.Val3;
