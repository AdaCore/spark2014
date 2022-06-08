package Util
  with Abstract_State => S,
       Initializes => S
is
   function Get return Boolean
     with Global   => S,
          Annotate => (GNATprove, Always_Return);

   procedure Toggle
     with Global   => (In_Out => S),
          Annotate => (GNATprove, Always_Return);
end Util;
