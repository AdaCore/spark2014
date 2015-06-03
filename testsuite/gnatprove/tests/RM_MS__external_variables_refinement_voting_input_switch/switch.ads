package Switch
  with SPARK_Mode,
       Abstract_State => (State with External => Async_Writers)
is
   type Reading is (on, off, unknown);

   function ReadValue return Reading
     with Volatile_Function,
          Global => (Input => State);
end Switch;
