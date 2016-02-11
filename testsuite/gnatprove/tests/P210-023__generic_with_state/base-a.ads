package Base.A with
   Abstract_State => (State,
                      (Atomic_State with External)),
   Elaborate_Body,
   SPARK_Mode
is
end Base.A;
