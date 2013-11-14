pragma SPARK_Mode (On);
package Switch
  with Abstract_State => (State with External => Async_Writers)
is
   type Reading is (on, off, unknown);

   function ReadValue return Reading
     with Global => (Input => State);
end Switch;
