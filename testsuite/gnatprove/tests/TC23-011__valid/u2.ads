package U2
  with SPARK_Mode => On,
       Abstract_State => (Port  with External => Async_Writers)
is

   procedure Read1 (X : out Character)
     with Global => (Input => Port),
          Depends => (X => Port);

   procedure Read2 (X : out Character)
     with Global => (Input => Port),
          Depends => (X => Port);

   procedure Read3 (X : out Character)
     with Global => (Input => Port),
          Depends => (X => Port);

   procedure Read4 (X : out Character)
     with Global => (Input => Port),
          Depends => (X => Port);
end U2;
