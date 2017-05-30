package B with
   Abstract_State => (State,
                      (Atomic_State with External))
is

   procedure Read_State (X : out Boolean);
   procedure Read_Atomic_State (X : out Boolean);

end B;
