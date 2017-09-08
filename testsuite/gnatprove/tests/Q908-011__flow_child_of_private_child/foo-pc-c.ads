package Foo.PC.C with
   SPARK_Mode,
   Abstract_State => (State with Part_Of => State_B),
   Initializes    => State
is

   procedure Wibble (X : Boolean;
                     Y : out Boolean)
   with Global => (In_Out => State);

end Foo.PC.C;
