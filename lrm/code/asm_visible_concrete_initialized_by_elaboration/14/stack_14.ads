package Stack_14
   with Abstract_State => (S, Pointer), -- concrete state
        Initializes    => (S, Pointer)
is
   procedure Push(X : in Integer)
      with Global => (In_Out => (S, Pointer));

   procedure Pop(X : out Integer)
      with Global => (Input  => S,
                      In_Out => Pointer);
end Stack_14;
