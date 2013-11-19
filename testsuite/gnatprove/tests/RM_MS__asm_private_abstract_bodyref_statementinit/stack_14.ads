package Stack_14
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => State
is
   procedure Push(X : in Integer)
     with Global => (In_Out => State);

   procedure Pop(X : out Integer)
     with Global => (In_Out => State);
end Stack_14;
