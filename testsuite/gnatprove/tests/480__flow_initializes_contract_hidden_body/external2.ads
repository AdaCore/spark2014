package External2
with
Abstract_State => State,
  Initializes => State
is
   pragma Elaborate_Body;

   X : Integer;

   function Get_State return Natural
   with
       Global => (Input => State),
       Import;

end External2;
