package Pkg
with
   SPARK_Mode,
   Abstract_State => State,
   Initializes    => State
is
   procedure Foo;

end Pkg;
