package External
with
Abstract_State => State,
  Initializes => State
is

   function Get_State return Natural
   with
       Global => (Input => State),
       Import;

end External;
