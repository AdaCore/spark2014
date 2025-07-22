package External3
with
Abstract_State => (State with External => Async_Writers),
  Initializes => State
is

   function Get_State return Natural
   with
       Global => (Input => State),
       Volatile_Function,
       Import;

end External3;
