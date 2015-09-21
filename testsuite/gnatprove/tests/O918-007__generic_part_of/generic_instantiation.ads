package Generic_Instantiation
with
   SPARK_Mode => On,
   Abstract_State => (State)
is

   procedure Write (Value : Natural)
   with
      Global => (Output => State);

end Generic_Instantiation;
