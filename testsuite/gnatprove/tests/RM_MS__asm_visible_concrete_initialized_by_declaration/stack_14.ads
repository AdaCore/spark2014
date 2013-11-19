package Stack_14
  with SPARK_Mode,
       Abstract_State => (S_State, Pointer_State),
       Initializes    => (S_State, Pointer_State)
is
   procedure Push(X : in Integer)
     with Global => (In_Out => (S_State, Pointer_State));

   procedure Pop(X : out Integer)
     with Global => (Input  => S_State,
                     In_Out => Pointer_State);
end Stack_14;
