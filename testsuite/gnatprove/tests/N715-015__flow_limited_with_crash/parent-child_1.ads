package Parent.Child_1
with Abstract_State => State
is
   pragma SPARK_Mode;

   procedure Initialise
     with Global => (Output => State);

end Parent.Child_1;
