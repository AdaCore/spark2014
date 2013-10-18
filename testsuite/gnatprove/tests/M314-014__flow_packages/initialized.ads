package Initialized
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => State
is
   function Get return Natural
     with Global => State;
end Initialized;
