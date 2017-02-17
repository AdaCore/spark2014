package Util
  with Abstract_State => S,
       Initializes => S
is
   function Get return Boolean
     with Global => S;

   procedure Toggle
     with Global => (In_Out => S);
end Util;

